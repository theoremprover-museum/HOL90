(defun change-type-quote ()
  "change one ml quote to a hol90 quote"
   (if (not(search-forward "\"\:" nil t)) nil
        (delete-backward-char 2)
        (insert-string "(==\`:")
        (search-forward "\"" nil t)
        (delete-backward-char 1)
        (insert-string "`==)") t))

(defun change-term-quote ()
  "change one ml quote to a hol90 quote"
   (if (not(search-forward "\"" nil t)) nil
       (delete-backward-char 1)
       (insert-string "(--\`")
       (search-forward "\"" nil t)
       (delete-backward-char 1)
       (insert-string "\`--)") t))

(defun change-quotes ()
  "change hol88 quotes to hol90 quotes"
  (beginning-of-buffer)
  (while (change-type-quote))
  (beginning-of-buffer)
  (while (change-term-quote)))

(defun swap-strings-and-quotes ()
  "changes all quotes to strings and vice-versa, with aid of intermediary"
  (beginning-of-buffer)
  (replace-string "\`" "..;..;;;..")
  (change-quotes)
  (beginning-of-buffer)
  (replace-string "..;..;;;.." "\""))


(defun change-type-variables ()
  "change hol88 type variables to hol90 type vars"
    (replace-string "******" "'f")
    (beginning-of-buffer)
    (replace-string "*****" "'e")
    (beginning-of-buffer)
    (replace-string "****" "'d")
    (beginning-of-buffer)
    (replace-string "***" "'c")
    (beginning-of-buffer)
    (replace-string "**" "'b")
    (beginning-of-buffer)
    (replace-string "*" "'a"))

(defun mk-one-sml-comment ()
  "change one ml comment to an sml comment. Doesn't know about nesting"
  (if (not (search-forward "%" nil t)) nil
      (delete-backward-char 1)
      (insert-string "(*")
      (if (not (search-forward "%" nil t)) nil
          (delete-backward-char 1)
          (insert-string "*)") t)))

(defun ml-to-sml-comments ()
   "change all ml comments in a buffer to sml comments"
    (while (mk-one-sml-comment)))

(defun ml-to-sml ()
  "first pass in converting a file from Classic ML to Standard ML"
  (beginning-of-buffer)
  (change-type-variables)
  (beginning-of-buffer)
  (ml-to-sml-comments)
  (beginning-of-buffer)
  (swap-strings-and-quotes)
  (beginning-of-buffer)
  (replace-string ";" ",")
  (beginning-of-buffer)
  (replace-string ",," ";")
  (beginning-of-buffer)
  (replace-regexp "letrec" "fun")
  (beginning-of-buffer)
  (replace-regexp "^let " "val ")
  (beginning-of-buffer))

