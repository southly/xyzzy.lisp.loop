;; Copyright (C) 2002-2004, Yuji Minejima <ggb01164@nifty.ne.jp>
;; ALL RIGHTS RESERVED.
;;
;; $Id: loop.l,v 1.3 2004/04/17 03:03:38 yuji Exp $
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 
;;  * Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;;  * Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in
;;    the documentation and/or other materials provided with the
;;    distribution.
;; 
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; 概要:
;;  Xyzzyエディタで、Common Lisp規格によって規定されている拡張loop構文を
;;  使えるようにするライブラリです。
;;
;;; インストール:
;;  ・変数*load-path*にリストアップされているディレクトリのどれか1つの
;;    中にloop.lを置いてください。*load-path*の内容は、
;;    `M-x describe-variable <RET> *load-path* <RET>'で調べられます。
;;  ・M-x byte-compile-file <RET> C:/path/to/loop.l <RET> として、loop.l
;;    をバイトコンパイルしてください。この結果、C:/path/to/loop.lcが作成
;;    されるはずです。
;;
;;; 使用:
;;  .xyzzy ファイルに次のコードを書き加えると、Xyzzyのセッション全体で
;;  拡張loop構文が有効になります。拡張loop構文は、普通の使い方をしている
;;  かぎり、Xyzzyで最初から定義されているloop構文と共存できるようになって
;;  いるので、問題はないと思います。(正確にはloopの次に続くS式がシンボルの
;;  時に、拡張loop構文として解釈されます。)
;;
;;    (require "loop")
;;    (use-package "loop")
;;
;;; 文献:
;; 拡張loop構文の正しい動作については、Common Lispの規格書を見てください。
;; Common Lisp Hyper Spec
;; http://www.lispworks.com/reference/HyperSpec/index.html
;; CLHS 6.1 The LOOP Facility
;; http://www.lispworks.com/reference/HyperSpec/Body/06_a.htm
;;
;;

(provide "loop")
(defpackage loop (:use lisp))
(in-package "loop")
;; Overwrite macro definition of lisp:loop. If you don't like this, do
;; (shadow '(loop)) .
(export '(loop loop-finish))

(defun %keyword (designator)
  (intern (string designator) 'keyword))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun %list (designator)
    (if (listp designator)
	designator
      (list designator))))

(defun %list (designator)
  (if (listp designator)
      designator
      (list designator)))

(defun constantly (value) #'(lambda (&rest rest) value))

(defmacro ecase (keyform &rest clauses)
  (let* ((clauses (mapcar #'(lambda (clause)
			      (let ((key (first clause))
				    (forms (rest clause)))
				`(,(%list key) ,@forms)))
			  clauses))
	 (expected-type `(member ,@(apply #'append (mapcar #'car clauses)))))
    `(case ,keyform
      ,@clauses
      (t (error 'type-error :datum ,keyform :expected-type ',expected-type)))))

(defvar *loop-clauses* (make-hash-table))
(defvar *for-as-subclauses* (make-hash-table))
(defvar *loop-name* nil)
(defvar *loop-keyword* nil)
(defvar *loop-raw-keyword* nil)
(defvar *it-var* nil)
(defvar *accumulation-clause-without-into-p* nil)
(defvar *boolean-clause-p* nil)
(defvar *loop-tokens*)
(defvar *loop-accumulators* nil)
(defvar *loop-template-fillers* (make-list 8))

(mapc
 #'(lambda (list)
     (let ((clause (pop list)))
       (mapc #'(lambda (key) (setf (gethash key *loop-clauses*) clause)) list)))
 '((for-as-clause :for :as)
   (with-clause :with)
   (do-clause :do)
   (return-clause :return)
   (initially-clause :initially)
   (finally-clause :finally)
   (accumulation-clause :collect :append :nconc :count :sum :maximize :minimize)
   (conditional-clause :if :when :unless)
   (repeat-clause :repeat)
   (always-never-thereis-clause :always :never :thereis)
   (while-clause :while)
   (until-clause :until)))

(mapc
 #'(lambda (list)
     (let ((clause (pop list)))
       (mapc #'(lambda (key) (setf (gethash key *for-as-subclauses*) clause))
	     list)))
 '((for-as-arithmetic-subclause
    :from :downfrom :upfrom :to :downto :upto :below :above :by)
   (for-as-in-list-subclause :in)
   (for-as-on-list-subclause :on)
   (for-as-equals-then-subclause :=)
   (for-as-across-subclause :across)
   (for-as-being-subclause :being)))

(defvar normalized-keywords
  '((:doing . :do)
    (:collecting . :collect)
    (:appending . :append)
    (:nconcing . :nconc)
    (:counting . :count)
    (:summing . :sum)
    (:maximizing . :maximize)
    (:minimizing . :minimize)))

(defun normalize-keyword (key) (or (cdr (assoc key normalized-keywords)) key))

(defun keyword-find (object keywords)
  (and (symbolp object)
       (find (normalize-keyword (%keyword object)) (%list keywords))))

(defun keyword? (&optional keys)
  (and *loop-tokens*
       (or (and (null keys) (symbolp (car *loop-tokens*)))
	   (keyword-find (car *loop-tokens*) keys))
       (setq *loop-raw-keyword* (%keyword (pop *loop-tokens*))
	     *loop-keyword* (normalize-keyword *loop-raw-keyword*))))

(defun keyword1 (&optional keys)
  (or (keyword? keys)
      (if (= 1 (length keys))
	  (error "loop keyword ~S is missing." (car keys))
	  (error "one of the loop keyword ~S must be supplied." keys))))

(defun clause ()
  (multiple-value-bind (clause-f present-p)
      (gethash *loop-keyword* *loop-clauses*)
    (unless present-p (error "Unknown loop keyword ~S" (string *loop-keyword*)))
    (funcall clause-f)))

(defun clause* ()
  (loop
   (let ((key (keyword?)))
     (unless key (return))
     (clause))))

(defun lp (&rest tokens)
  (let ((*loop-tokens* tokens)
	(*loop-keyword* *loop-keyword*))
    (clause*)
    (when *loop-tokens* (error "~S remained after lp" *loop-tokens*))))

(defun preposition? (&optional keys) (let (*loop-keyword*) (keyword? keys)))
(defun preposition1 (&optional keys) (let (*loop-keyword*) (keyword1 keys)))

(defun form1 ()
  (unless *loop-tokens* (error "a normal lisp form is missing."))
  (pop *loop-tokens*))

(defun compound-forms* ()
  (when (and *loop-tokens* (consp (car *loop-tokens*)))
    (cons (pop *loop-tokens*) (compound-forms*))))

(defun compound-forms+ ()
  (or (compound-forms*) (error "At least one compound form is needed.")))

(defun simple-var-p (var) (and var (symbolp var)))

(defun simple-var1 ()
  (unless (and *loop-tokens* (simple-var-p (car *loop-tokens*)))
    (error "a simple variable name is missing."))
  (pop *loop-tokens*))

(defun d-var-spec-p (spec)
  (or (simple-var-p spec)
      (null spec)
      (and (listp spec) (d-var-spec-p (car spec)) (d-var-spec-p (cdr spec)))))

(defun d-var-spec1 ()
  (unless (and *loop-tokens* (d-var-spec-p (car *loop-tokens*)))
    (error "a destructured-type-spec is missing"))
  (pop *loop-tokens*))

(defun destructured-type-spec (&optional (default-type t))
  (cond
    ((preposition? :of-type)
     (when (null *loop-tokens*)
       (error "OF-TYPE keyword should be followed by a type spec."))
     (pop *loop-tokens*))
    ((and *loop-tokens* (member (car *loop-tokens*) '(fixnum float t nil)))
     (pop *loop-tokens*))
    (t default-type)))

(defun car-type (types) (if (consp types) (car types) types))
(defun cdr-type (types) (if (consp types) (cdr types) types))
(defun var-default-value (var type)
  (if (consp var)
      (cons (var-default-value (car var) (car-type type))
	    (var-default-value (cdr var) (cdr-type type)))
      (cond
	((subtypep type 'integer) 0)
	((subtypep type 'float) 0.0)
	((subtypep type 'number) 0)
	((subtypep type 'character) #\space)
	((subtypep type 'string) "")
	((subtypep type 'vector) #())
	(t nil))))

(defun destruct-var-type-spec (d-var-spec d-type-spec initial-value-form)
  (let (temp-stack var-stack)
    (labels
	((empty-p (tree)
	   (or (null tree)
	       (and (consp tree) (empty-p (car tree)) (empty-p (cdr tree)))))
	 (dig (var type exp temp)
	   (cond
	     ((empty-p var) nil)
	     ((simple-var-p var)
	      (when temp (push temp temp-stack))
	      (push (list type var exp) var-stack))
	     ((empty-p (car var))
	      (dig (cdr var) (cdr-type type) `(cdr ,exp) temp))
	     ((empty-p (cdr var))
	      (when temp (push temp temp-stack))
	      (dig (car var) (car-type type) `(car ,exp) nil))
	     (t (unless temp (setq temp (or (pop temp-stack) (gensym))))
		(dig (car var) (car-type type) `(car (setq ,temp ,exp)) nil)
		(dig (cdr var) (cdr-type type) `(cdr ,temp) temp)))))
      (dig d-var-spec d-type-spec initial-value-form nil)
      (values (mapcar #'(lambda (v) `(t ,v nil)) (reverse temp-stack))
              (reverse var-stack)))))

(defun fill-in (&key vars inits iterators initially body steps finally return)
  (mapl #'(lambda (l v) (setf (car l) (append (car l) (car v))))
	*loop-template-fillers*
	(list vars inits iterators initially body steps finally return)))

(defun with (var &optional (type t) &key (= (var-default-value var type)))
  (fill-in :vars `((,type ,var ,=))))

(defun with-clause ()
  (let (var type value-form temp temps vars)
    (loop
     (setq var (d-var-spec1)
	   type (destructured-type-spec)
	   value-form (if (preposition? :=) (form1) `',(var-default-value var type))
	   temp (gensym)
	   temps (append temps (list (list t temp value-form))))
     (multiple-value-bind (t1 v1) (destruct-var-type-spec var type temp)
       (setq vars (append vars t1 v1)))
     (unless (preposition? :and) (return)))
    (fill-in :vars (append temps vars))))

(defun dispatch-for-as-subclause (var type)
  (unless *loop-tokens*
    (error "a preposition for a FOR-AS subclause is missing."))
  (let ((prep (preposition1)))
    (multiple-value-bind (subclause present-p) (gethash prep *for-as-subclauses*)
      (unless present-p
	(error "Unknown preposition ~S for FOR-AS subclause." prep))
      (push prep *loop-tokens*)
      (funcall subclause var type))))

(defun for-as (var type &rest rest)
  (let ((*loop-tokens* rest))
    (dispatch-for-as-subclause var type)))

(defun for-as-clause ()
  (let (*vars* *temp-vars* *temp-inits* *inits* *temp-steps* *steps*)
    (declare (special *vars* *temp-vars* *temp-inits* *inits*
                      *temp-steps* *steps*))
    (loop (dispatch-for-as-subclause (d-var-spec1) (destructured-type-spec))
          (unless (preposition? :and) (return)))
    (fill-in :vars  (append *temp-vars* *vars*)
             :inits `((setq ,@(append *temp-inits* *inits*)))
	     :steps `((setq ,@(append *temp-steps* *steps*))))))

(defun for-as-equals-then-subclause (var type)
  ;; 6.1.1.4 Expanding Loop Forms
  ;; http://www.lispworks.com/reference/HyperSpec/Body/06_aad.htm
  ;; the form1 and form2 in a for-as-equals-then form includes the lexical
  ;; environment of all the loop variables.
  (declare (special *temp-vars* *vars* *temp-inits* *inits*
                    *temp-steps* *steps*))
  (preposition1 :=)
  (let* ((first (form1))
	 (then  (if (preposition? :then) (form1) first))
         (temp (gensym)))
    (with temp t := `',(var-default-value var type))
    (multiple-value-bind (temps vars) (destruct-var-type-spec var type temp)
      (setq *temp-vars* (append *temp-vars* temps)
            *temp-inits* (apply #'append *temp-inits* `(,temp ,first)
                                (mapcar #'cdr temps))
	    *temp-steps* (apply #'append *temp-steps* `(,temp ,then)
                                (mapcar #'cdr temps))
            *vars* (append *vars* vars)
	    *inits* (apply #'append *inits* (mapcar #'cdr vars))
	    *steps* (apply #'append *steps* (mapcar #'cdr vars))))))

(defun for-as-arithmetic-prepositions (selected)
  (append (cond
	    ((intersection '(:from :downfrom :upfrom) selected) nil)
 	    ((intersection '(:downto :above) selected) '(:from :downfrom))
	    ((intersection '(:upto :below) selected) '(:from :upfrom))
	    (t '(:from :downfrom :upfrom)))
	  (cond
	    ((intersection '(:to :downto :upto :below :above) selected) nil)
	    ((find :upfrom selected) '(:to :upto :below))
	    ((find :downfrom selected) '(:to :downto :above))
	    (t '(:to :downto :upto :below :above)))
	  (unless (find :by selected) '(:by))))

(defun for-as-arithmetic-subclause (var type)
  (declare (special *vars* *steps*))
  (let (selected temp from to by preps)
    (loop (or (setq preps (for-as-arithmetic-prepositions selected)) (return))
          (push (or (preposition? preps) (return)) selected)
          (with (setq temp (gensym)) 'number := (form1))
          (case (car selected)
            ((:from :downfrom :upfrom) (setq from temp))
            ((:to :downto :upto :below :above) (setq to temp))
            (:by (setq by temp))))
    (when (null selected)
      (error "One of the prepositions ~S is needed"
             (for-as-arithmetic-prepositions nil)))
    (let* ((up-p (subsetp selected '(:below :upto :upfrom :from :to :by)))
           (test (cond ((member :to selected) (if up-p #'> #'<))
                       ((member :upto selected) #'>)
                       ((member :below selected) #'>=)
                       ((member :downto selected) #'<)
                       ((member :above selected) #'<=)
                       (t (constantly nil))))
           (next `(,(if up-p '+ '-) ,var ,(or by 1))))
      (fill-in :inits `((when (funcall ,test ,var ,to) (loop-finish))))
      (setq *vars* (append *vars* `((,type ,var ,(or from 0))))
            *steps* (append *steps* `(,var (if (funcall ,test ,next ,to)
                                               (loop-finish)
                                               ,next)))))))
	   
(defun by-step-fun ()
  (if (not (preposition? :by))
      #'cdr
      (let ((step-fun-form (form1)))
	(if (functionp step-fun-form)
	    step-fun-form
	    (let* ((step-fun (gensym)))
	      (with step-fun t := step-fun-form)
	      step-fun)))))

(defun for-as-on-list-subclause (var type)
  (preposition1 :on)
  (let ((temp (gensym)))
    (with temp t := (form1))
    ;; check with atom. see 6.1.2.1.3 The for-as-on-list subclause
    ;; http://www.lispworks.com/reference/HyperSpec/Body/06_abac.htm
    (for-as var type := `(if (atom ,temp) (loop-finish) ,temp)
                     :then `(if (atom (setq ,temp
                                       (funcall ,(by-step-fun) ,temp)))
                             (loop-finish) ,temp))))

(defun for-as-in-list-subclause (var type)
  (preposition1 :in)
  (let ((temp (gensym)))
    (with temp t := (form1))
    ;; check with endp. see 6.1.2.1.2 The for-as-in-list subclause
    ;; http://www.lispworks.com/reference/HyperSpec/Body/06_abab.htm
    (for-as var type := `(if (endp ,temp) (loop-finish) (car ,temp))
                     :then `(if (endp (setq ,temp
                                       (funcall ,(by-step-fun) ,temp)))
                             (loop-finish) (car ,temp)))))

(defun for-as-across-subclause (var type)
  (preposition1 :across)
  (let* ((vector (gensym))
	 (i (gensym)))
    (with vector 'vector := (form1))
    (lp :for i :from 0 :below `(length ,vector))
    (for-as var type := `(aref ,vector ,i))))

(defun using-other-var (key)
  (let ((using (when (preposition? :using) (pop *loop-tokens*)))
	(other-key (if (find key '(:hash-key :hash-keys))
		       :hash-value
		       :hash-key)))
    (when using
      ;;(assert (string= (first using) other-key))
      ;; assert not supported in 0.2.2.233
      (unless (string= (first using) other-key)
	(error "using-other-var: internal logic error."))
      (second using))))

(defun for-as-being-subclause (var type)
  (preposition1 :being)
  (preposition1 '(:each :the))
  (let* ((hash-spec '(:hash-key :hash-keys :hash-value :hash-values))
	 (symbol-spec '(:symbol :symbols :present-symbol :present-symbols
			:external-symbol :external-symbols))
	 (key (preposition1 (append hash-spec symbol-spec)))
         (container (gensym))           ; hash or package
	 (iterator (gensym)))
    (cond
      ((find key hash-spec)
       (preposition1 '(:in :of))
       (with container 'hash-table := (form1))
       (fill-in :iterators `((with-hash-table-iterator (,iterator ,container))))
       (let* ((other-var (using-other-var key))
	      (key-p (find key '(:hash-key :hash-keys)))
	      (var  (if key-p `(,var ,other-var) `(,other-var ,var)))
	      (type (if key-p `(,type t) `(t ,type))))
	 (for-as var type := `(multiple-value-bind (more key value)
			       (,iterator)
			       (if more (list key value) (loop-finish))))))
      ((find key symbol-spec)
       (let* ((package-form (if (preposition? '(:in :of)) (form1) '*package*))
	      (kinds (ecase key
		       ((:symbol :symbols) '(:internal :external :inherited))
		       ((:present-symbol :present-symbols)
			'(:internal :external))
		       ((:external-symbol :external-symbols) '(:external)))))
         (with container 'package := package-form)
	 (fill-in :iterators
                  `((with-package-iterator (,iterator ,container ,@kinds))))
	 (for-as var type := `(multiple-value-bind (more symbol)
			       (,iterator)
			       (if more symbol (loop-finish))))))
      (t (error "Internal logic error")))))

(defun form-or-it ()
  (if (preposition? :it)
      (or *it-var* (setq *it-var* (gensym)))
      (form1)))

(defun accumulator (name)
  (let* ((type (destructured-type-spec (if (find *loop-keyword*
						 '(:collect :append :nconc))
					   'list 'number)))
	 (assoc (assoc name *loop-accumulators*)))
    (if assoc
	(let ((keys (remove-duplicates (getf (third assoc) :keys)))
	      (set (find *loop-keyword* '((:collect :append :nconc)
					  (:sum :count)
					  (:maximize :minimize))
			 :test #'member)))
	  (unless (subsetp keys set)
	    (error "Can't mix accumulator ~S with ~S" *loop-keyword* keys)))
	(let ((var (or name (gensym)))
	      (plist (list :keys (list *loop-keyword*))))
	  (with var type)
	  (case *loop-keyword*
	    ((:collect :append :nconc)
	     (let ((splice (gensym)))
	       (setf (getf plist :splice) splice)
	       (with splice 'list := nil)))
	    ((:maximize :minimize)
	     (let ((first-p (gensym)))
	       (setf (getf plist :first-p) first-p)
	       (with first-p t := t))))
	  (push (setq assoc (list name var plist)) *loop-accumulators*)
	  (unless name (fill-in :return `(,var)))))
    (values (second assoc) (third assoc))))

;(define-condition ambiguous-loop-result-error (program-error)
;  ((format-control :reader loop-error-format-control :initarg :format-control)
;   (format-arguments :reader loop-error-format-arguments
;                     :initarg :format-arguments)))

(defun ambiguous-loop-result-error ()
  (error "~S cannot be used without `into' preposition with ~S"
	 *accumulation-clause-without-into-p* *boolean-clause-p*))

(defun accumulation-clause ()
  (let* ((form (form-or-it))
	 (name (if (preposition? :into)
                   (simple-var1)
                   (progn
                     (setq *accumulation-clause-without-into-p* *loop-keyword*)
                     (when *boolean-clause-p* (ambiguous-loop-result-error))
                     nil))))
    (multiple-value-bind (var plist) (accumulator name)
      (ecase *loop-keyword*
	((:collect :append :nconc)
	 (let ((splice (getf plist :splice))
	       (fun (ecase *loop-keyword*
		      (:collect 'list)
		      (:append 'copy-list)
		      (:nconc 'identity))))
	   (lp :do `(if ,splice
		     (setf (cdr ,splice) (,fun ,form) ,splice (last ,splice))
		     (setf ,var (,fun ,form) ,splice (last ,var))))))
	(:count (lp :if form :do `(incf ,var)))
	(:sum (lp :do `(incf ,var ,form)))
	((:maximize :minimize)
	 (let ((first-p (getf plist :first-p))
	       (fun (if (eq *loop-keyword* ':maximize) '< '>)))
	   (lp :do `(let ((value ,form))
		     (cond
		       (,first-p (setq ,first-p nil ,var value))
		       ((,fun ,var value) (setq ,var value)))))))))))

(defun return-clause () (lp :do `(return-from ,*loop-name* ,(form-or-it))))

    
(defun do-clause () (fill-in :body (compound-forms+)))

(defun selectable-clause ()
  (ecase *loop-keyword*
    ((:if :when :unless) (conditional-clause))
    (:do (do-clause))
    ((:return) (return-clause))
    ((:collect :append :nconc :count :sum :maximize :minimize)
     (accumulation-clause))))

(defun conditional-clause ()
  (let* ((*it-var* nil)
	 (middle (gensym))
	 (bottom (gensym))
	 (test-form (if (eq *loop-keyword* :unless) `(not ,(form1)) (form1)))
	 (condition-form `(unless ,test-form (go ,middle))))
    (lp :do condition-form)
    (loop (keyword1) (selectable-clause) (unless (preposition? :and) (return)))
    (cond
      ((preposition? :else)
       (lp :do `(go ,bottom))
       (fill-in :body `(,middle))
       (loop (keyword1)
	     (selectable-clause)
	     (unless (preposition? :and) (return)))
       (fill-in :body `(,bottom)))
      (t (fill-in :body `(,middle))))
    (preposition? :end)
    (when *it-var*
      (with *it-var*)
      (setf (second condition-form)
	    `(setq ,*it-var* ,(second condition-form))))))

(defun initially-clause () (fill-in :initially (compound-forms+)))
(defun finally-clause () (fill-in :finally (compound-forms+)))
(defun while-clause () (lp :unless (form1) :do '(loop-finish) :end))
(defun until-clause () (lp :while `(not ,(form1))))
(defun repeat-clause () (lp :for (gensym) :from 0 :below (form1)))
(defun always-never-thereis-clause ()
  (setq *boolean-clause-p* *loop-keyword*)
  (when *accumulation-clause-without-into-p* (ambiguous-loop-result-error))
  (ecase *loop-keyword*
    (:always (lp :unless (form1) :return nil :end) (fill-in :return '(t)))
    (:never (lp :always `(not ,(form1))))
    (:thereis (lp :if (form1) :return :it :end) (fill-in :return '(nil)))))

(defun variable-clause* ()
  (loop (let ((key (keyword? '(:with :initially :finally :for :as))))
	  (if key (clause) (return)))))

(defun main-clause* ()
  (loop
   (if (keyword? '(:do :return :if :when :unless :initially :finally
		   :while :until :repeat :always :never :thereis
		   :collect :append :nconc :count :sum :maximize :minimize))
       (clause)
       (return))))

(defun name-clause? ()
  (when (keyword? :named)
    (unless *loop-tokens* (error "A loop name is missing."))
    (let ((name (pop *loop-tokens*)))
      (unless (symbolp name)
	(error "~S cannot be a loop name which must be a symbol." name))
      (setq *loop-name* name))))

(define-condition double-binding-error (program-error)
  ((variable :reader double-binding-error-variable :initarg :variable))
  (:report (lambda (condition stream)
	     (format stream "variable ~S is bound more than once."
		     (double-binding-error-variable condition)))))

(defun with-iterators (iterators form)
  (if iterators
      (append (car iterators) (list (with-iterators (cdr iterators) form)))
      form))

(defmacro extended-loop (&rest forms)
  (let ((*loop-name* nil)
	(*loop-tokens* forms)
	(*loop-keyword*)
	(*loop-template-fillers* (make-list 8))
	(*loop-accumulators* nil)
        (*accumulation-clause-without-into-p* nil)
        (*boolean-clause-p* nil)
	(body-tag (gensym))
	(epilogue-tag (gensym)))
    (name-clause?)
    (variable-clause*)
    (main-clause*)
    (when *loop-tokens*
      (error "Loop tokens ~S are remained unprocessed." *loop-tokens*))
    (multiple-value-bind (vars inits iterators initially body steps
                               finally return)
	(apply #'values *loop-template-fillers*)
      (mapl #'(lambda (x)
		(when (find (first x) (rest x))
		  (error 'double-binding-error :variable (first x))))
	    (mapcar #'second vars))
      `(block ,*loop-name*
	(let* (,@(mapcar #'cdr vars))
	  (declare ,@(mapcar #'(lambda (x) (cons 'type (butlast x))) vars))
	  (macrolet ((loop-finish () '(go ,epilogue-tag)))
            ,(with-iterators iterators
               `(tagbody
                 ,@inits
                 ,@initially
                 ,body-tag
                 ,@body
                 ,@steps
                 (go ,body-tag)
                 ,epilogue-tag
                 ,@finally
                 (return-from ,*loop-name* ,(car return))))))))))

(defmacro simple-loop (&rest compound-forms)
  (let ((top (gensym)))
    `(block nil
      (tagbody
	 ,top
	 ,@compound-forms
	 (go ,top)))))

(defmacro loop (&rest forms)
  (if (symbolp (car forms))
      `(extended-loop ,@forms)
      `(simple-loop ,@forms)))
