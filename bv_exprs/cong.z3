(set-option :smt.arith.solver 6)
(set-option :smt.arith.nl.gb true)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const n Int)
(assert 
	(not
		(implies
			(and
				(not (= n 0))
				(= (mod b n) (mod a n))
			)
			(= (mod (* a c) n) (mod (* b c) n))
		)
	)
)
(check-sat)