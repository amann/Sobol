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
                               :element-type '(simple-array #2#)
                               :initial-element (make-array 0 :element-type '#2#)))
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
      (declare (type (unsigned-byte 8) idx))))

  (declaim (ftype (function (#0# #3=(integer 1 #.array-total-size-limit) t)
                            (simple-array #5=(simple-array #4=(signed-byte #.(1+ #1#)))))
                  sobol-points))
  (defun sobol-sequences (nbr-points dimension file)
    "Return NBR-POINTS sobol points of dimension DIMENSION using the primitive polynomials file FILE.

NBR-POINTS must be of the form 2^k - 1 with 0 < k <= 20 and DIMENSION must be below ARRAY-TOTAL-SIZE-LIMIT."
    (declare (optimize (speed 3) (debug 0))
             (type #0# nbr-points)
             (type #3# dimension))
    (let ((grid (let ((arrays (make-array dimension :element-type '#5#
                                                    :initial-element (make-array 0 :element-type '#4#))))
                  (dotimes (i dimension arrays)
                    (setf (aref arrays i)
                          (make-array nbr-points :element-type '#4#))))))
      (let* ((direction-numbers (compute-direction-numbers
                                 (read-polynomials file dimension)
                                 nbr-points))
             (2^31 (expt 2 (1- (integer-length nbr-points)))))
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
(declaim (ftype (function ((vector vector)) rational)
                discrepancy))
(defun discrepancy (sobol-sequences)
  (let* ((dimension (length sobol-sequences))
         (nbr-points (1+ (length (aref sobol-sequences 0))))
         (origin (- (expt 2 (1- (integer-length (1- nbr-points))))))
         (total-volume (expt (- (* origin 2)) dimension)))
    (multiple-value-bind (fn l)
        (cartesian-product* sobol-sequences)
      (declare (type (function (vector integer) vector)))
      (let* ((sup 0)
             (sup-lock (bt2:make-lock :name "SUP")))
        (p-dotimes (i l sup)
            ((corner-point (make-array dimension :element-type '(signed-byte 32)
                                                 :initial-element (- origin))))
          (funcall fn corner-point i)
          (let ((volume-ratio (/ (volume-interval origin corner-point)
                                 total-volume)))
            (multiple-value-bind (count-open count-closed)
                (count-points sobol-sequences corner-point)
              (let ((max (max (abs (- (/ count-open
                                         nbr-points)
                                      volume-ratio))
                              (abs (- (/ count-closed
                                         nbr-points)
                                      volume-ratio)))))
                (bt2:with-lock-held (sup-lock)
                  (setf sup (max sup max)))))))))))

(declaim (ftype (function ((signed-byte 32) vector) integer)))
(defun volume-interval (origin corner-point)
  (declare (type (signed-byte 32) origin))
  (reduce (lambda (r x)
            (declare (type (signed-byte 32) x)
                     (type integer r))
            (* r (- x origin)))
          corner-point
          :initial-value 1))

(declaim (ftype (function ((vector vector) vector) (values fixnum fixnum))
                count-points))
(defun count-points (sobol-sequences corner-point
                     &aux
                       (nbr-points (length (aref sobol-sequences 0)))
                       (dimension (length sobol-sequences)))
  (declare (type (vector vector) sobol-sequences))
  (let ((open 0)
        (closed 0)
        (point (make-array dimension :element-type '(signed-byte 32))))
    (declare (type fixnum open closed)
             (dynamic-extent point))
    (dotimes (i nbr-points (values open closed))
      (dotimes (j dimension)
        (setf (aref point j) (aref (aref sobol-sequences j) i)))
      (multiple-value-bind (in-open-p in-closed-p)
          (point-in-interval-p point corner-point)
        (when in-open-p
          (incf open))
        (when in-closed-p
          (incf closed))))))

(defun point-in-interval-p (sobol-point corner-point
                            &aux
                              (dimension (length corner-point))
                              (pack-size 8))
  (declare (type (vector (signed-byte 32)) sobol-point corner-point))
  (multiple-value-bind (open closed)
      (flet ((handle-stump (open closed start)
               (declare (type sb-simd-avx2:u32.8 open closed)
                        (type fixnum start))
               (let ((point (avx2-s32.8-stump sobol-point start 0))
                     (corner (avx2-s32.8-stump corner-point start 1)))
                 (declare (type sb-simd-avx2:s32.8 point corner))
                 (values
                  (sb-simd-avx2:u32.8-and open
                                          (sb-simd-avx2:s32.8< point
                                                               corner))
                  (sb-simd-avx2:u32.8-and closed
                                          (sb-simd-avx2:s32.8<= point
                                                                corner))))))
        (if (< dimension pack-size)
            (handle-stump (sb-simd-avx2:u32.8 sb-simd-avx2:+u32-true+)
                          (sb-simd-avx2:u32.8 sb-simd-avx2:+u32-true+)
                          0)
            (do ((limit (* (floor dimension pack-size) pack-size))
                 (d pack-size (+ d pack-size))
                 (point (sb-simd-avx2:s32.8-aref sobol-point 0)
                        (sb-simd-avx2:s32.8-aref sobol-point d))
                 (corner (sb-simd-avx2:s32.8-aref corner-point 0)
                         (sb-simd-avx2:s32.8-aref corner-point d))
                 (open (sb-simd-avx2:u32.8 sb-simd-avx2:+u32-true+)
                       (sb-simd-avx2:u32.8-and open
                                               (sb-simd-avx2:s32.8< point
                                                                    corner)))
                 (closed (sb-simd-avx2:u32.8 sb-simd-avx2:+u32-true+)
                         (sb-simd-avx2:u32.8-and closed
                                                 (sb-simd-avx2:s32.8<= point
                                                                       corner))))
                ((<= limit d)
                 (handle-stump open closed d)))))
    (values
     (= sb-simd-avx2:+u32-true+ (multiple-value-call
                                    'sb-simd-avx2:u32-and
                                  (sb-simd-avx2:u32.8-values open)))
     (= sb-simd-avx2:+u32-true+ (multiple-value-call
                                    'sb-simd-avx2:u32-and
                                  (sb-simd-avx2:u32.8-values closed))))))


(defun avx2-s32.8-stump (vector start default-value)
  (declare (type (vector sb-simd-avx2:s32) vector)
           (type fixnum start)
           (type sb-simd-avx2:s32 default-value))
  (let ((stump (make-array 8 :element-type 'sb-simd-avx2:s32
                             :initial-element default-value)))
    (declare (dynamic-extent stump))
    (sb-simd-avx2:s32.8-aref (dotimes (i (min 8 (- (length vector) start)) stump)
                               (setf (aref stump i)
                                     (aref vector (+ i start))))
                             0)))


(defun scale-sobol-points (sobol-points)
  (let ((factor (coerce (expt 2
                              (1+ (integer-length (length (svref sobol-points
                                                                 0)))))
                        'single-float)))
    (map '(vector (vector single-float))
         (lambda (x)
           (map '(vector single-float)
                (lambda (x)
                  (/ (coerce x 'single-float)
                     factor))
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

(declaim (type (vector vector) *sobol*))
(defparameter *sobol*
  (sobol-sequences (1- (expt 2 9))
                   (expt 2 5)
                   #p"c:/Users/amao/projects/Sobol/new-joe-kuo-6.21201"))

(defun check-corr ()
  (let* ((max 0)
         (dim (length *sobol*))
         (prod (make-array (length (svref *sobol* 0))))
         (sum (* 1/4 (expt 2 32) dim)))
    (dotimes (i dim (/ max sum))
      (let ((sobol_i (aref *sobol* i)))
        (dotimes (j i)
          (setf max (max max
                         (abs (- (reduce '+ (map-into prod '*
                                                      sobol_i
                                                      (aref *sobol*
                                                             j)))
                                 sum)))))
        (when (zerop (mod i 100))
          (format t "~%~A: ~A" i (/ max sum)))))))

(defun sym-index (i j)
  (declare (type (integer 0) i j))
  (cond ((< i j) (sym-index j i))
        (t (+ (/ (* (1+ i) i) 2) j))))
(defstruct (symmetric-matrix
            (:constructor make-symmetric-matrix
                (dimension &optional (initial-element 0.0)
                 &aux
                   (data (make-array (sym-index dimension 0)
                                     :element-type 'single-float
                                     :initial-element initial-element)))))
  dimension
  data)
(defmethod mref ((matrix symmetric-matrix) row col)
  (with-slots (data)
      matrix
    (declare (type vector data))
    (aref data (sym-index row col))))
(defsetf mref (matrix row col) (value)
  (alexandria:with-gensyms (data matrix-var)
    `(let ((,matrix-var ,matrix))
       (declare (type symmetric-matrix ,matrix-var))
       (with-slots ((,data data))
           ,matrix-var
         (declare (type vector ,data))
         (setf (aref ,data (sym-index ,row ,col)) ,value)))))

(defun correlation-matrix (&optional (*sobol* *sobol*)
                           &aux (sobol (scale-sobol-points *sobol*)))
  (declare (optimize (speed 3) (debug 0)))
  (let* ((sobol-0 (aref sobol 0))
         (dim (length sobol))
         (var (fma-f32+* sobol-0 sobol-0)))
    (declare (type vector sobol sobol-0)
             (type single-float var))
    (let ((matrix (make-symmetric-matrix dim 1.0)))
      (p-dotimes (i dim matrix) ()
        (let ((sobol-i (aref sobol i)))
          (dotimes (j i)
            (setf (mref matrix i j) (/ (fma-f32+* sobol-i (aref sobol j))
                                       var))))))))
(declaim (type symmetric-matrix *corells*))
(defparameter *correls* (make-symmetric-matrix 1 1.0))


(defun classify-correlations ()
  (declare (optimize (speed 3) (debug 0)))
  (let ((hash (make-hash-table))
        (dim (length *sobol*))
        (correlation-matrix (correlation-matrix)))
    (dotimes (i dim)
      (dotimes (j i)
        (push j (getf (gethash (abs (mref correlation-matrix i j))
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
  (map 'vector
       (let ((row-idx -1))
         (declare (type fixnum row-idx))
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
  (let* ((correls *correls*)
         (nbr-dims (symmetric-matrix-dimension correls))
         (i 0))
    (flet ((too-big (j)
             (< threshold (mref correls i j))))
      (do* ((dims (loop :for j :from 1 :below nbr-dims :collect j))
            (result (when (notany #'too-big dims)
                      (list i))))
           ((or (null dims) (<= nbr-dims i)) result)
        (setf dims (remove-if #'too-big dims))
        (incf i)
        (when (and dims (= i (car dims)))
          (push (pop dims) result))))))

