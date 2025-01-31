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

(defun compute-direction-numbers (polynomials nbr-points)
  (let ((l (integer-length nbr-points))
        result)
    (dolist (item polynomials (coerce (nreverse result) 'vector))
      (push (let* ((a (car item))
                   (m (cdr item))
                   (s (length m))
                   (v (make-array l)))
              (dotimes (k (min l s))
                (setf (svref v k) (ash (svref m k) (- 31 k))))
              (dotimes (k (- l s) v)
                (let* ((v_k (svref v k))
                       (v_k+s (logxor v_k (ash v_k (- s))))
                       (k+s (+ k s)))
                  (setf (svref v k+s)
                        (dotimes (r (- s 1) v_k+s)
                          (setf v_k+s
                                (logxor v_k+s
                                        (if (ldb-test (byte 1 (- s 2 r))
                                                      a)
                                            (svref v (- k+s 1 r))
                                            0))))))))
            result))))

(defun zero@idx (integer)
  (declare (type (unsigned-byte 64) integer)
           (optimize (speed 3) (safety 3) (debug 0)))
  (do ((idx 0 (1+ idx)))
      ((not (ldb-test (byte 1 idx) integer)) idx)
    (declare ((unsigned-byte 8) idx))))

(defun sobol-points (nbr-points dimension file)
  (let ((grid (make-array dimension :initial-contents (let (arrays)
                                                        (dotimes (i dimension arrays)
                                                          (push (make-array nbr-points) arrays))))))
    (let ((direction-numbers (compute-direction-numbers (read-polynomials file dimension)
                                                        nbr-points))
          (2^32 (coerce (expt 2 32) 'double-float)))
      (dotimes (d (length direction-numbers) grid)
        (let ((v (svref direction-numbers d))
              (x_d (svref grid d))
              (x 0))
          (dotimes (n nbr-points)
            (setf (svref x_d n) (/ (setf x (logxor x (svref v (zero@idx n))))
                                   2^32))))))))

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

(defparameter *sobol* (sobol-points (1- (expt 2 9)) (expt 2 11) #p"../new-joe-kuo-6.21201"))

(defun check-corr ()
  (let* ((max 0)
         (dim (length *sobol*))
         (prod (make-array (length (svref *sobol* 0))))
         (sum (* 1/4 (expt 2 32) dim)))
    (dotimes (i dim (/ max sum))
      (let ((sobol_i (svref *sobol* i)))
        (dotimes (j i)
          (setf max (max max (abs (- (reduce '+ (map-into prod '*
                                                          sobol_i
                                                          (svref *sobol* j)))
                                     sum)))))
        (when (zerop (mod i 100))
          (format t "~%~A: ~A" i (/ max sum)))))))
