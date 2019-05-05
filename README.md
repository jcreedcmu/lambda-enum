diagram.png
===

In the first column are five particular maps.

In the second column are those same maps, with certain selected subterm edges indicated with red underline, labelled by the set of free variables in them. The unsatisfiable task is: globally choose a color for all paths, such that all of these red-underlined edges obtain a valid color. (i.e. the klein-4-group sum of the colors of their free variables is not the identity element of that group)

In the third column I've indicated the paths to the variables involved in those subterms, and numbered the distinct paths 1 through 6 for brevity.

In the fourth column I've rewritten the constraints in terms of the arbitrary convenient path numbering.

So the unsatisfiable problem can be phrased as

```
(declare-const BBBBF (_ BitVec 2))
(declare-const BBBBAF (_ BitVec 2))
(declare-const BBBBAFF (_ BitVec 2))
(declare-const BBBBAFA (_ BitVec 2))
(declare-const BBBBAABF (_ BitVec 2))
(declare-const BBBBAABAF (_ BitVec 2))

(assert (not (= #b00 BBBBF)))
(assert (not (= #b00 BBBBAF)))
(assert (not (= #b00 BBBBAFF)))
(assert (not (= #b00 BBBBAFA)))
(assert (not (= #b00 BBBBAABF)))
(assert (not (= #b00 BBBBAABAF)))

(assert (not (= #b00 (bvxor BBBBF BBBBAF))))                    ; ////@*@*@/@***
(assert (not (= #b00 (bvxor BBBBAFF BBBBAFA))))                 ; ////@(/@**)(@(@**)*)
(assert (not (= #b00 (bvxor BBBBF BBBBAFF BBBBAFA))))           ; ////@*@@**/@**
(assert (not (= #b00 (bvxor BBBBAABF BBBBAABAF))))              ; ////@*@*/@*@**
(assert (not (= #b00 (bvxor BBBBAF BBBBAABF BBBBAABAF))))       ; ////@*@*/@*@**
(assert (not (= #b00 (bvxor BBBBF BBBBAF BBBBAABF BBBBAABAF)))) ; ////@*@*/@*@**
(assert (not (= #b00 (bvxor BBBBAFF BBBBAFA BBBBAABF))))        ; ////@*@@**/@**
(assert (not (= #b00 (bvxor BBBBF BBBBAFF BBBBAFA BBBBAABF))))  ; ////@*@@**/@**

(check-sat)
(get-model)
```

Or, alpha-equivalently,

```
(declare-const v1 (_ BitVec 2)) (assert (not (= #b00 v1)))
(declare-const v2 (_ BitVec 2)) (assert (not (= #b00 v2)))
(declare-const v3 (_ BitVec 2)) (assert (not (= #b00 v3)))
(declare-const v4 (_ BitVec 2)) (assert (not (= #b00 v4)))
(declare-const v5 (_ BitVec 2)) (assert (not (= #b00 v5)))
(declare-const v6 (_ BitVec 2)) (assert (not (= #b00 v6)))

(assert (not (= #b00 (bvxor v1 v2))))
(assert (not (= #b00 (bvxor v3 v4))))
(assert (not (= #b00 (bvxor v1 v3 v4))))
(assert (not (= #b00 (bvxor v5 v6))))
(assert (not (= #b00 (bvxor v2 v5 v6))))
(assert (not (= #b00 (bvxor v1 v2 v5 v6))))
(assert (not (= #b00 (bvxor v3 v4 v5))))
(assert (not (= #b00 (bvxor v1 v3 v4 v5))))

(check-sat)
(get-model)
```
