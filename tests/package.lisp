

(in-package :cl-user)

(defpackage :cl-vknots-tests
  (:use :alexandria :cl :cl-vknots :fiveam #:iterate)
  (:export #:run-tests))

(in-package :cl-vknots-tests)

(defun run-tests ()
  (let ((results (run 'cl-vknots)))
    (fiveam:explain! results)
    (unless (fiveam:results-status results)
      (error "Tests failed."))))

