\ Every term-tag set made by core/terms.fs's lf-tags (plan 9.4.8n (3),
\ branches reuse-b and reuse-c) against the OR chain of tag comparisons
\ it replaced, written out here as it stood (the [kernel]-in-form rule:
\ identical results), on every tag from -2 to 40 and on extreme values;
\ and each set's members pinned, so that a set that loses or gains a tag
\ fails here (review of reuse-b, finding 5). Loads src/main.fs.
require ../support/tester.fs
require ../../src/main.fs

\ The old chains, one per set.
: =any ( tag t1 t2 -- flag ) >r over = swap r> = or ;
: old-binary ( tag -- flag )
  dup lf-tag-app = over lf-tag-lam = or over lf-tag-pi = or over lf-tag-let = or
  over lf-tag-projection = or swap lf-tag-let-nondep = or ;
: old-binder ( tag -- flag ) lf-tag-lam lf-tag-pi =any ;
: old-let ( tag -- flag ) lf-tag-let lf-tag-let-nondep =any ;
: old-literal ( tag -- flag ) lf-tag-lit lf-tag-str =any ;
: old-sort ( tag -- flag ) lf-tag-sort lf-tag-symbolic-sort =any ;
: old-fvar-mvar ( tag -- flag ) lf-tag-fvar lf-tag-mvar =any ;
: old-whnf-normal ( tag -- flag )
  dup lf-tag-lam = over lf-tag-pi = or over lf-tag-constant = or
  over lf-tag-bvar = or over old-literal or swap lf-tag-symbolic-sort = or ;
: old-whnf-easy ( tag -- flag )
  dup lf-tag-bvar = over lf-tag-pi = or over old-literal or swap lf-tag-symbolic-sort = or ;
: old-dd-false ( tag -- flag ) dup old-binder over old-let or swap lf-tag-constant = or ;
: old-pp-app ( tag -- flag ) lf-tag-app lf-tag-projection =any ;
: old-pp-leaf-kind ( tag -- flag )
  dup old-fvar-mvar over old-literal or swap lf-tag-proj = or ;
: old-pp-pair-kind ( tag -- flag ) dup lf-tag-projection = swap old-let or ;
: old-pp-applied ( tag -- flag )
  dup old-pp-app over lf-tag-bvar = or over lf-tag-fvar = or swap lf-tag-constant = or ;
: old-pp-leaf ( tag -- flag )
  dup old-sort over lf-tag-constant = or over lf-tag-proj = or
  over old-fvar-mvar or swap old-literal or ;
: old-sought ( tag -- flag )
  dup lf-tag-app = over lf-tag-projection = or over lf-tag-bvar = or
  over lf-tag-symbolic-sort = or over lf-tag-constant = or over lf-tag-lit = or
  swap lf-tag-proj = or ;
: old-before-ie ( tag -- flag )
  dup lf-tag-app = over lf-tag-bvar = or over lf-tag-constant = or swap lf-tag-pi = or ;
: old-mck ( tag -- flag ) lf-tag-projection lf-tag-annotation =any ;
: old-kab ( tag -- flag ) dup old-let swap lf-tag-annotation = or ;
: old-meq-one-head ( tag -- flag ) lf-tag-constant lf-tag-symbolic-sort =any ;
: old-nest-restore ( tag -- flag ) lf-tag-app lf-tag-constant =any ;

\ The tags tried: -2 .. 40, then the extremes.
create extremes max-n , max-n invert , 63 , 64 , -1 , 0 , 31 , 32 ,
: agrees-on? ( tag xt-new xt-old -- flag ) >r over swap execute swap r> execute = ;
: agree? ( xt-new xt-old -- flag )
  true 41 -2 do >r 2dup i -rot agrees-on? r> and loop
  8 0 do >r 2dup extremes i cells + @ -rot agrees-on? r> and loop nip nip ;
\ A set used through lf-tag-in?, as a predicate.
: in-binary ( tag -- flag ) lf-binary-tags lf-tag-in? ;
: in-sort ( tag -- flag ) lf-sort-tags lf-tag-in? ;
: in-literal ( tag -- flag ) lf-literal-tags lf-tag-in? ;
: in-let ( tag -- flag ) lf-let-tags lf-tag-in? ;
: in-whnf-easy ( tag -- flag ) lf-whnf-easy-tags lf-tag-in? ;
: in-dd-false ( tag -- flag ) dd-false-tags lf-tag-in? ;
: in-pp-app ( tag -- flag ) lf-pp-app-tags lf-tag-in? ;
: in-pp-leaf-kind ( tag -- flag ) lf-pp-leaf-kinds lf-tag-in? ;
: in-pp-pair-kind ( tag -- flag ) lf-pp-pair-kinds lf-tag-in? ;
: in-pp-leaf ( tag -- flag ) lf-pp-leaf-tags lf-tag-in? ;
: in-pp-applied ( tag -- flag ) lf-pp-applied-tags lf-tag-in? ;
: in-sought ( tag -- flag ) lfa-sought-tags lf-tag-in? ;
: in-before-ie ( tag -- flag ) lfx-before-ie lf-tag-in? ;
: in-mck ( tag -- flag ) mck-unported lf-tag-in? ;
: in-kab ( tag -- flag ) kab-unported lf-tag-in? ;
: in-meq-one-head ( tag -- flag ) lf-meq-one-head-tags lf-tag-in? ;
: in-nest-restore ( tag -- flag ) lf-nest-restore-tags lf-tag-in? ;
: in-fvar-mvar ( tag -- flag ) lf-fvar-mvar-tags lf-tag-in? ;

\ core/terms.fs, let-terms.fs, string-literals.fs, tagged-sort-boundary.fs,
\ mvar-leaves.fs.
T{ ' lf-term-binary-tag? ' old-binary agree? ' in-binary ' old-binary agree? -> true true }T
T{ ' lf-term-binder-tag? ' old-binder agree? ' lf-term-let-tag? ' old-let agree? -> true true }T
T{ ' in-let ' old-let agree? ' lf-literal-tag? ' old-literal agree? ' in-literal ' old-literal agree?
   -> true true true }T
T{ ' in-sort ' old-sort agree? ' lf-fvar-mvar-tag? ' old-fvar-mvar agree? ' in-fvar-mvar ' old-fvar-mvar agree?
   -> true true true }T
\ kernel/whnf.fs, mixed-compare.fs, inductive-nested.fs ([kernel] in form).
T{ ' lf-whnf-normal? ' old-whnf-normal agree? ' in-whnf-easy ' old-whnf-easy agree? -> true true }T
T{ ' in-meq-one-head ' old-meq-one-head agree? ' in-nest-restore ' old-nest-restore agree? -> true true }T
\ front/defeq-delta.fs, meta-check.fs, kabstract.fs.
T{ ' dd-false? ' old-dd-false agree? ' in-dd-false ' old-dd-false agree? -> true true }T
T{ ' in-mck ' old-mck agree? ' in-kab ' old-kab agree? -> true true }T
\ present/print-analysis.fs, print-names.fs, term-printer.fs.
T{ ' lf-pp-app-tag? ' old-pp-app agree? ' in-pp-app ' old-pp-app agree? -> true true }T
T{ ' lf-pp-leaf-kind? ' old-pp-leaf-kind agree? ' in-pp-leaf-kind ' old-pp-leaf-kind agree? -> true true }T
T{ ' lf-pp-pair-kind? ' old-pp-pair-kind agree? ' in-pp-pair-kind ' old-pp-pair-kind agree? -> true true }T
T{ ' lf-pp-applied-tag? ' old-pp-applied agree? ' in-pp-applied ' old-pp-applied agree? -> true true }T
T{ ' in-pp-leaf ' old-pp-leaf agree? -> true }T
\ author/build.fs, export.fs.
T{ ' in-sought ' old-sought agree? ' in-before-ie ' old-before-ie agree? -> true true }T

\ Each set's members, pinned by count: a set that loses or gains a tag
\ fails even where its users' tests do not reach that tag.
: members ( mask -- n ) 0 41 -2 do over i swap lf-tag-in? - loop nip ;
T{ lf-binary-tags members lf-binder-tags members lf-let-tags members lf-literal-tags members
   -> 6 2 2 2 }T
T{ lf-sort-tags members lf-fvar-mvar-tags members lf-whnf-normal-tags members lf-whnf-easy-tags members
   -> 2 2 7 5 }T
T{ dd-false-tags members dd-simple-tags members mck-unported members kab-unported members -> 5 7 2 3 }T
T{ lf-pp-app-tags members lf-pp-leaf-kinds members lf-pp-pair-kinds members lf-pp-leaf-tags members
   lf-pp-applied-tags members -> 2 5 3 8 5 }T
T{ lfa-sought-tags members lfx-before-ie members lf-meq-one-head-tags members lf-nest-restore-tags members
   -> 7 4 2 2 }T

\ lf-term-in? reads the term's tag, not the index (the reviewer's fault
\ that reduced it to lf-tag-in? survived tests/core/terms.fs): a Sort and
\ an application, whose indices are not their tags.
0 lf-term-bvar drop constant a-var
0 lf-term-sort drop constant a-sort
a-var a-sort lf-term-app drop constant an-app
T{ a-sort lf-sort-tags lf-term-in? an-app lf-sort-tags lf-term-in? a-sort lf-sort? an-app lf-sort? -> true false true false }T
T{ an-app lf-binary-tags lf-term-in? a-sort lf-binary-tags lf-term-in? -> true false }T
bye
