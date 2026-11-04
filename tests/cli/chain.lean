-- A correct theorem whose export is larger than `leanforth check --record`
-- holds (64 names, levels and term nodes per export): that ends full on
-- tests/cli/chain.ndjson, exit 3, while `leanforth check`, whose stores
-- grow, accepts it (docs/user/COMMAND_LINE.md). Exported with
-- scripts/export.sh; tests/cli/export-check.sh rebuilds the export and its
-- manifest and compares them with the committed files.
theorem chain {A B C D E F G H I J K L M : Prop}
    (f1 : A → B) (f2 : B → C) (f3 : C → D) (f4 : D → E) (f5 : E → F) (f6 : F → G)
    (f7 : G → H) (f8 : H → I) (f9 : I → J) (f10 : J → K) (f11 : K → L) (f12 : L → M) :
    A → M :=
  fun a => f12 (f11 (f10 (f9 (f8 (f7 (f6 (f5 (f4 (f3 (f2 (f1 a)))))))))))

#print axioms chain
