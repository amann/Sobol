(in-package #:cl-user)

(asdf:defsystem #:sobol
  :name "SOBOL"
  :author "amao"
  :depends-on (#:sb-simd #:eager-future2)
  :components ((:module "src"
                :components
                ((:file "package")
                 (:file "utils")
                 (:file "sobol"))))
  :serial t)
