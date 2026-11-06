; Adapted from BIRD SQL Mini-Dev, question_id 297, student_club.
; BIRD SQL team, CC BY-SA 4.0: https://creativecommons.org/licenses/by-sa/4.0/
; https://huggingface.co/datasets/birdsql/bird_mini_dev
; Revision: 5b256b5a9c17478f06ed6912612e9a14d17065c8
; SELECT notes FROM income
; WHERE source='Fundraising' AND date_received='2019-09-14'
; Layout: [notes, source, date_received]. Compare combined/nested filters.
(define-fun source_test () SqlPred
  (sql.eq (sql.column 1) (sql.text "Fundraising")))
(define-fun date_test () SqlPred
  (sql.eq (sql.column 2) (sql.text "2019-09-14")))
(assert (distinct
  (sql.project (sql.one (sql.column 0))
    (sql.filter (sql.and source_test date_test) (sql.scan "income")))
  (sql.project (sql.one (sql.column 0))
    (sql.filter source_test (sql.filter date_test (sql.scan "income"))))))
