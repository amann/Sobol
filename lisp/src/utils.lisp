(in-package #:sobol)

(defun cartesian-product (sequence &rest other-sequences)
  (cartesian-product* (apply 'vector sequence other-sequences)))

(declaim (ftype (function ((vector vector))
                          (values (function (vector integer) vector)
                                  integer fixnum))
                cartesian-product*))
(defun cartesian-product* (all-sequences)
  (declare (type (vector vector) all-sequences))
  (let* ((basis (map '(vector fixnum) 'length all-sequences))
         (total-length (reduce '* basis))
         (rank (length all-sequences)))
    (setf (aref basis (1- rank)) 1)
    (values
     (lambda (v i)
       (declare (type vector v)
                (type integer i))
       (let ((s-index -1))
         (declare (type fixnum s-index))
         (map-into v (lambda (index)
                       (declare (type fixnum index))
                       (aref (aref all-sequences (incf s-index)) index))
                   (the vector
                        (decompose-to-basis-into v i basis)))))
     total-length
     rank)))

(declaim (ftype (function (vector integer (vector fixnum))
                          (vector fixnum))
                decompose-to-basis))
(defun decompose-to-basis-into (vector n basis)
  "337, '(4 5 3 1) --> #(5 2 2 1), i.e. 337 = 5 * (* 4 5 3 1) + 2 * (* 5 3 1) + 2 * (* 3 1) + 1 * (* 1)"
  (declare (type vector vector)
           (type integer n))
  (map-into vector
            (let ((p (reduce '* basis)))
              (declare (type integer p))
              (lambda (b)
                (declare (type fixnum b))
                (multiple-value-bind (k r)
                    (floor n p)
                  (prog1
                      k
                    (setf p (/ p b)
                          n r)))))
            basis))



;;;; ==== SIMD ====

(defun f32+* (vector0 vector1)
  (sb-simd:instruction-set-case
    (:fma (fma-f32+* vector0 vector1))
    (:sse4.2 (sse4.2-f32+* vector0 vector1))))

(defun sse4.2-f32+* (vector0 vector1)
  (declare (type (simple-array sb-simd-sse4.2:f32) vector0 vector1))
  (let ((length (min (length vector0) (length vector1))))
    (multiple-value-call 'sb-simd-sse4.2:f32+
      (sb-simd-sse4.2:f32.4-values
       (do ((i 0 (+ i 8))
            (sum (sb-simd-sse4.2:f32.4 0.0)
                 (sb-simd-sse4.2:f32.4+ (sb-simd-sse4.2:f32.4* (sb-simd-sse4.2:f32.4-aref vector0 i)
                                                               (sb-simd-sse4.2:f32.4-aref vector1 i))
                                        sum)))
           ((<= length i) sum)
         (declare (dynamic-extent sum)))))))

(defun fma-f32+* (vector0 vector1)
  (declare (type (simple-array sb-simd-fma:f32) vector0 vector1))
  (let ((end (* (floor (min (length vector0) (length vector1)) 8) 8)))
    (multiple-value-call 'sb-simd-fma:f32+
      (sb-simd-fma:f32.8-values
       (do ((i 0 (+ i 8))
            (sum (sb-simd-fma:f32.8 0.0)
                 (sb-simd-fma:f32.8-fmadd (sb-simd-fma:f32.8-aref vector0 i)
                                          (sb-simd-fma:f32.8-aref vector1 i)
                                          sum)))
           ((<= end i)
            (sb-simd-fma:f32.8-fmadd (fma-f32.8-stump vector0 i 0.0)
                                     (fma-f32.8-stump vector1 i 0.0)
                                     sum))
         (declare (dynamic-extent sum)))))))


(defun fma-f32.8-stump (vector start default-value)
  (declare (type (vector sb-simd-fma:f32) vector)
           (type fixnum start)
           (type sb-simd-fma:f32 default-value))
  (let ((stump (make-array 8 :element-type 'sb-simd-fma:f32
                             :initial-element default-value)))
    (declare (dynamic-extent stump))
    (sb-simd-fma:f32.8-aref (dotimes (i (min 8 (- (length vector) start)) stump)
                              (setf (aref stump i)
                                    (aref vector (+ i start))))
                            0)))

;;;; ==== Loops ====

(defvar *nbr-threads* 15)
(defmacro p-dotimes ((var count &optional result)
                     (&rest thread-specific-bindings)
                     &body body)
  (alexandria:with-gensyms (count-var start end index i
                                      nbr-threads threads nbr-active-threads
                                      finished act-on)
    `(let* ((,count-var ,count)
            (,nbr-threads *nbr-threads*)
            (,threads (make-array ,nbr-threads))
            (,nbr-active-threads (bt2:make-atomic-integer :value ,nbr-threads))
            (,finished (bt2:make-semaphore)))
       (declare (special *nbr-threads*))
       (flet ((,act-on (,start ,end)
                (lambda ()
                  (let ,thread-specific-bindings
                    (do* ((,i ,start (1+ ,i))
                          (,var ,i ,i))
                         ((<= ,end ,i)
                          (when (zerop (bt2:atomic-integer-decf ,nbr-active-threads))
                            (bt2:signal-semaphore ,finished)))
                      (declare (ignorable ,var))
                      ,@body)))))
         (handler-case
             (progn
               (do-partitions (,index ,start ,end)
                   (,count-var ,nbr-threads)
                 (setf (aref ,threads ,index)
                       (bt2:make-thread (,act-on ,start ,end))))
               (bt2:wait-on-semaphore ,finished))
           (error (err)
             (map nil (lambda (thread)
                        (when (bt2:thread-alive-p thread)
                          (bt2:destroy-thread thread)))
                  ,threads)
             (bt2:signal-semaphore ,finished)
             (error err))))
       (let ((,var ,count-var))
         (declare (ignorable ,var))
         ,result))))



(defmacro do-partitions ((index-var start-var end-var)
                         (total-number number-partitions)
                         &body body)
  (let ((number (gensym "NUMBER"))
        (divisor (gensym "DIVISOR"))
        (cursor (gensym "CURSOR"))
        (k (gensym "K"))
        (r (gensym "R"))
        (i (gensym "I")))
    `(let ((,number ,total-number)
           (,divisor ,number-partitions))
       (multiple-value-bind (,k ,r)
           (floor ,number ,divisor)
         (let ((,cursor 0))
           (dotimes (,i ,divisor)
             (let ((,index-var ,i)
                   (,start-var ,cursor)
                   (,end-var (incf ,cursor (+ ,k (if (< ,i ,r) 1 0)))))
               ,@body)))))))



(defmacro while (condition &body body)
  (let ((start '#:start))
    `(tagbody
        ,start
        (when ,condition
          ,@body
          (go ,start)))))
