-- The Lean twin of c-sy-check.lf (plan row S3, slice S3a-ops): pinned Lean's
-- #check of the same terms; check.py --lean requires its output to be the
-- lines check.py --init requires of LeanForth.
#check 3 ∣ 12
#check Dvd.dvd 3 12
#check 2 ^ 10
#check 2 ^ 3 ^ 2
#check 10 - 3 < 10 /\ 17 / 5 = 3
