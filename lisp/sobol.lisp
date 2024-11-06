(defpackage #:sobol
  (:nicknames #:s)
  (:use #:cl))

(in-package #:sobol)

(defun read-polynomials (file dimension)
  (with-open-file (*standard-input* file)
    (read-line)
    (do* ((d 1 (read))
          (s 32 (read))
          (a 0 (read))
          (m (make-array s :initial-element 1)
             (let ((m (make-array s)))
               (dotimes (i s m)
                 (setf (svref m i) (read)))))
          (result (list (cons a m))
                  (cons (cons a m) result)))
         ((<= dimension d) (nreverse result)))))

(eval-when (:compile-toplevel :load-toplevel :execute)
;;;; #0# = (integer 1 2^20-1)
;;;; #1# = 20,
;;;; #2# = (unsigned-byte 20)
  (declaim (ftype (function (sequence #0=(integer 1 #.(1- (expt 2 #1=#.(floor (integer-length most-positive-fixnum) 3)))))
                            (simple-array (simple-array #2=(unsigned-byte #1#))))))
  (defun compute-direction-numbers (polynomials nbr-points)
    (declare (optimize (speed 3) (debug 0))
             (type #2# nbr-points))
    (let* ((l (integer-length nbr-points))
           (nbr-polynomials (length polynomials))
           (result (make-array nbr-polynomials
                               :element-type '(simple-array #2#)))
           (i -1))
      (dolist (item polynomials result)
        (setf (aref result (incf i))
              (let* ((a (car item))
                     (m (cdr item))
                     (s (length m))
                     (v (make-array l :element-type '#2#)))
                (declare (type simple-vector m)
                         (type (unsigned-byte 16) s a))
                (dotimes (k (min l s))
                  (setf (aref v k) (the #2#
                                        (ash (the #2#
                                                  (svref m k))
                                             (- l 1 k)))))
                (dotimes (k (- l s) v)
                  (let* ((k+s (+ k s))
                         (k+s-1 (- k+s 1))
                         (v_k (aref v k))
                         (v_k+s (logxor v_k (ash v_k (- s)))))
                    (declare (type #2#
                                   v_k v_k+s k k+s k+s-1))
                    (setf (aref v k+s)
                          (dotimes (r (- s 1) v_k+s)
                            (setf v_k+s
                                  (logxor v_k+s
                                          (if (ldb-test (byte 1 (- s
                                                                   2
                                                                   r))
                                                        a)
                                              (the #2#
                                                   (aref v (- k+s-1
                                                               r)))
                                              0))))))))))))

  (declaim (ftype (function (#2#) (unsigned-byte 8)) zero@idx))
  (defun zero@idx (integer)
    (declare (type #2# integer)
             (optimize (speed 3) (safety 3) (debug 0)))
    (do ((idx 0 (1+ idx)))
        ((not (ldb-test (byte 1 idx)
                        integer))
         idx)
      (declare ((unsigned-byte 8) idx))))

  (declaim (ftype (function (#0# #3=(integer 1 #.array-total-size-limit) t)
                            (simple-array #5=(simple-array #4=(signed-byte #.(1+ #1#)))))
                  sobol-points))
  (defun sobol-sequences (nbr-points dimension file)
    "Return NBR-POINTS sobol points of dimension DIMENSION using the primitive polynomials file FILE.

NBR-POINTS must be of the form 2^k - 1 with 0 < k <= 20 and DIMENSION must be below ARRAY-TOTAL-SIZE-LIMIT."
    (declare (optimize (speed 3) (debug 0))
             (type #0# nbr-points)
             (type #3# dimension))
    (let ((grid (let ((arrays (make-array dimension :element-type '#5#)))
                  (dotimes (i dimension arrays)
                    (setf (aref arrays i)
                          (make-array nbr-points :element-type '#4#))))))
      (let* ((direction-numbers (compute-direction-numbers
                                 (read-polynomials file dimension)
                                 nbr-points))
             (2^31 (expt 2 (1- (integer-length nbr-points))))
             (thread-pool-size (eager-future2:thread-pool-size)))
        (dotimes (d (length direction-numbers) grid)
          (let ((v (aref direction-numbers d))
                (x_d (aref grid d))
                (x 0))
            (declare (type #2# x))
            (dotimes (n nbr-points)
              (setf (aref x_d n)
                    (- (setf x (logxor x
                                       (the #2#
                                            (aref v (zero@idx n)))))
                       2^31)))))))))
(defun discrepancy (sobol-sequences)
  (let* ((dimension (length sobol-sequences))
         (nbr-points (length (aref sobol-sequences 0)))
         (origin (print (- (expt 2 (1- (integer-length nbr-points))))))
         (total-volume (print (expt (- (* origin 2)) dimension))))
    (let* ((corner-point (make-array dimension :element-type '(signed-byte 32)
                                               :initial-element (- origin)))
           (sup 0))
      (multiple-value-bind (fn l)
          (cartesian-product* sobol-sequences)
        (dotimes (i l sup)
          (print (funcall fn corner-point i))
          (setf sup (max sup
                         (print
                          (abs (- (print (/ (multiple-value-call 'max (count-points sobol-sequences corner-point))
                                            (1+ nbr-points)))
                                  (print (/ (volume-interval origin corner-point)
                                            total-volume))))))))))))
(defun volume-interval (origin corner-point)
  (reduce (lambda (r x)
            (* r (- x origin)))
          corner-point
          :initial-value 1))
(defun count-points (sobol-sequences corner-point
                     &aux
                       (nbr-points (length (aref sobol-sequences 0)))
                       (dimension (length sobol-sequences)))
  (let ((open 0)
        (closed 0)
        (point (make-array dimension :element-type '(signed-byte 32))))
    (declare (dynamic-extent point))
    (dotimes (i nbr-points (values open closed))
      (dotimes (j dimension)
        (setf (aref point j) (aref (aref sobol-sequences j) i)))
      (multiple-value-bind (in-open-p in-closed-p)
          (point-in-interval-p point corner-point)
        (when in-open-p
          (incf open))
        (when in-closed-p
          (incf closed))))))

(defun point-in-interval-p (point corner-point
                            &aux
                              (dimension (length corner-point))
                              (pack-size 8))
  (declare (type (simple-array (signed-byte 32)) point corner-point))
  (multiple-value-bind (open closed)
      (do ((limit (* (floor dimension pack-size) pack-size))
           (d 0 (+ d pack-size))
           (open (sb-simd-avx2:u32.8 sb-simd-avx2:+u32-true+)
                 (sb-simd-avx2:u32.8-and open
                                         (sb-simd-avx2:s32.8< (sb-simd-avx2:s32.8-aref point d)
                                                              (sb-simd-avx2:s32.8-aref corner-point d))))
           (closed (sb-simd-avx2:u32.8 sb-simd-avx2:+u32-true+)
                   (sb-simd-avx2:u32.8-and closed
                                           (sb-simd-avx2:s32.8<= (sb-simd-avx2:s32.8-aref point d)
                                                                 (sb-simd-avx2:s32.8-aref corner-point d)))))
          ((<= limit d)
           (let ((d (max 0 (- dimension pack-size))))
             (values
              (sb-simd-avx2:u32.8-and open
                                      (sb-simd-avx2:s32.8< (avx2-s32.8-stump point d 0)
                                                           (avx2-s32.8-stump corner-point d 1)))
              (sb-simd-avx2:u32.8-and closed
                                      (sb-simd-avx2:s32.8<= (avx2-s32.8-stump point d 0)
                                                            (avx2-s32.8-stump corner-point d 1)))))))
    (values
     (= sb-simd-avx2:+u32-true+ (multiple-value-call
                                    'sb-simd-avx2:u32-and
                                  (sb-simd-avx2:u32.8-values open)))
     (= sb-simd-avx2:+u32-true+ (multiple-value-call
                                    'sb-simd-avx2:u32-and
                                  (sb-simd-avx2:u32.8-values closed))))))


(defun avx2-s32.8-stump (vector start default-value)
  (let ((stump (make-array 8 :element-type 'sb-simd-avx2:s32
                             :initial-element default-value)))
    (declare (dynamic-extent stump))
    (sb-simd-avx2:s32.8-aref (dotimes (i (min 8 (- (length vector) start)) stump)
                             (setf (aref stump i)
                                   (aref vector (+ i start))))
                             0)))

(defun cartesian-product (sequence &rest other-sequences
                          &aux)
  (cartesian-product* (apply 'vector sequence other-sequences)))
(defun cartesian-product* (all-sequences)
  (let* ((basis (map 'vector 'length all-sequences))
         (total-length (reduce '* basis))
         (length-basis (length all-sequences)))
    (setf (aref basis (1- length-basis)) 1)
    (values
     (lambda (v i)
       (declare (type array v)
                (type integer i))
       (let ((indices (make-array length-basis :element-type 'fixnum))
             (s-index -1))
         (declare (dynamic-extent indices))
         (map-into v (lambda (index)
                       (aref (aref all-sequences (incf s-index)) index))
                   (decompose-to-basis-into indices i basis))))
     total-length
     length-basis)))

(declaim (ftype (function ((array fixnum) integer sequence)
                          (simple-array fixnum))
                decompose-to-basis))
(defun decompose-to-basis-into (vector n basis)
  "337, '(4 5 3 1) --> #(5 2 2 1), i.e. 337 = 5 * (* 4 5 3 1) + 2 * (* 5 3 1) + 2 * (* 3 1) + 1 * (* 1)"
  (declare (type (array fixnum) vector))
  (map-into vector
            (let ((p (reduce '* basis)))
              (lambda (b)
                (declare (type fixnum b))
                (multiple-value-bind (k r)
                    (floor n p)
                  (prog1
                      k
                    (setf p (/ p b)
                          n r)))))
            basis))

(defun shift-and-scale-sobol-points (sobol-points)
  (let ((factor (expt 2 (1+ (integer-length (length (svref sobol-points 0)))))))
    (map 'vector (lambda (x)
                   (map 'vector (lambda (x)
                                  (+ (/ x factor) 1/2))
                        x))
         sobol-points)))

(defun mean (sequence)
  (let* ((count 0)
         (sum (reduce (lambda (r x)
                        (incf count)
                        (+ r x))
                      sequence
                      :initial-value 0)))
    (if (zerop count)
        0
        (/ sum count))))

(declaim (type simple-vector *sobol*))
(defparameter *sobol* (sobol-sequences (1- (expt 2 9))
                                       (expt 2 12)
                                       #p"./new-joe-kuo-6.21201"))

(defun check-corr ()
  (let* ((max 0)
         (dim (length *sobol*))
         (prod (make-array (length (svref *sobol* 0))))
         (sum (* 1/4 (expt 2 32) dim)))
    (dotimes (i dim (/ max sum))
      (let ((sobol_i (svref *sobol* i)))
        (dotimes (j i)
          (setf max (max max
                         (abs (- (reduce '+ (map-into prod '*
                                                      sobol_i
                                                      (svref *sobol*
                                                             j)))
                                 sum)))))
        (when (zerop (mod i 100))
          (format t "~%~A: ~A" i (/ max sum)))))))

(defun correlation-matrix (&optional (*sobol* *sobol*))
  (declare (optimize (speed 3) (debug 0)))
  (let* ((sobol-0 (svref *sobol* 0))
         (n (length sobol-0))
         (dim (length *sobol*))
         (prod (make-array n)))
    (declare (type simple-vector *sobol* sobol-0))
    (flet ((sum-xy (x y)
             (reduce (lambda (r xy)
                       (declare (type (signed-byte 128) r)
                                (type (signed-byte 64) xy))
                       (+ r xy))
                     (map-into prod
                               (lambda (x y)
                                 (declare (type (signed-byte 32)
                                                x y))
                                 (the (signed-byte 64) (* x y)))
                               x y)
                     :initial-value 0)))
      (declare (ftype (function (simple-vector simple-vector)
                                (signed-byte 128))
                      sum-xy))
      (let ((sum-x_i^2 (coerce (sum-xy sobol-0 sobol-0)
                               'double-float)))
        (declare (type double-float sum-x_i^2))
        (map-into (make-array dim)
                  (lambda (sobol-i)
                    (declare (type simple-vector sobol-i))
                    (map-into (make-array dim)
                              (lambda (sobol-j)
                                (declare (type simple-vector
                                               sobol-j))
                                (/ (the (signed-byte 128)
                                        (sum-xy sobol-i sobol-j))
                                   (the double-float sum-x_i^2)))
                              *sobol*))
                  *sobol*)))))
(declaim (type simple-vector *corells*))
(defparameter *correls* (make-array 0))


(defun classify-correlations ()
  (declare (optimize (speed 3) (debug 0)))
  (let ((hash (make-hash-table))
        (dim (length *sobol*))
        (correlation-matrix (correlation-matrix)))
    (dotimes (i dim)
      (dotimes (j i)
        (push j (getf (gethash (abs (the rational (svref (svref correlation-matrix j) i)))
                               hash)
                      i))))
    (let (result)
      (maphash (lambda (k v)
                 (push (cons k (list v)) result))
               hash)
      (sort result '> :key 'car))))

(defun filter-scenarii-with-big-corr (threshold
                                      &optional
                                        (*correls* *correls*))
  (map 'vector (let ((row-idx -1))
                 (lambda (row)
                   (incf row-idx)
                   (let ((list (make-array 0 :adjustable t
                                             :fill-pointer t))
                         (col-idx -1))
                    (map nil
                         (lambda (c)
                           (when (and (not (= row-idx
                                              (incf col-idx)))
                                      (<= threshold c))
                             (vector-push-extend (cons col-idx c)
                                                 list)))
                         row)
                     list)))
       *correls*))


(defun filter-correls (&optional (threshold 0.015) (*correls* *correls*))
 (let* (
        (nbr-dims (length *correls*))
        (i 0)
        (row (svref *correls* i))
        result)
   (flet ((too-big (j)
            (< threshold (svref row j))))
     (do* ((dims (loop :for i :from 1 :below nbr-dims :collect i)))
          ((or (null dims) (<= nbr-dims i)) result)
       (setf dims (remove-if #'too-big dims))
       (incf i)
       (setf row (svref *correls* i))
       (when (and dims (= i (car dims)))
         (push (pop dims) result))))))


(defpackage #:sobol-internal
  (:use #:cl #:sb-simd-avx2))

(in-package #:sobol-internal)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (setf (get 's8.32 :aref)  's8.32-aref
        (get 's8.32 :+)     's8.32+
        (get 's8.32 :*)     's8.32*
        (get 's16.16 :aref) 's16.16-aref
        (get 's16.16 :+)    's16.16+
        (get 's16.16 :*)    's16.16*
        (get 's32.8 :aref)  's32.8-aref
        (get 's32.8 :+)     's32.8+
        (get 's32.8 :*)     's32.8*
        (get 's64.4 :aref)  's64.4-aref
        (get 's64.4 :+)     's64.4+
        (get 's64.4 :*)     's64.4*
        (get 'f32.8 :aref)  'f32.8-aref
        (get 'f32.8 :+)     'f32.8+
        (get 'f32.8 :*)     'f32.8*
        (get 'f64.4 :aref)  'f64.4-aref
        (get 'f64.4 :+)     'f64.4+
        (get 'f64.4 :*)     'f64.4*))


(defun correlation-matrix ())

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
  (let ((length (min (length vector0) (length vector1))))
    (multiple-value-call 'sb-simd-fma:f32+
      (sb-simd-fma:f32.8-values
       (do ((i 0 (+ i 8))
            (sum (sb-simd-fma:f32.8 0.0)
                 (sb-simd-fma:f32.8-fmadd (sb-simd-fma:f32.8-aref vector0 i)
                                          (sb-simd-fma:f32.8-aref vector1 i)
                                          sum)))
           ((<= length i) sum)
         (declare (dynamic-extent sum)))))))





(eager-future2:thread-pool-size)
