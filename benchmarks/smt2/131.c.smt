(set-logic LIA)

( declare-const d1 Int )
( declare-const d1! Int )
( declare-const d2 Int )
( declare-const d2! Int )
( declare-const d3 Int )
( declare-const d3! Int )
( declare-const x1 Int )
( declare-const x1! Int )
( declare-const x2 Int )
( declare-const x2! Int )
( declare-const x3 Int )
( declare-const x3! Int )

( declare-const d1_0 Int )
( declare-const d2_0 Int )
( declare-const d3_0 Int )
( declare-const x1_0 Int )
( declare-const x1_1 Int )
( declare-const x1_2 Int )
( declare-const x1_3 Int )
( declare-const x2_0 Int )
( declare-const x2_1 Int )
( declare-const x2_2 Int )
( declare-const x2_3 Int )
( declare-const x3_0 Int )
( declare-const x3_1 Int )
( declare-const x3_2 Int )
( declare-const x3_3 Int )

( define-fun inv-f( ( d1 Int )( d2 Int )( d3 Int )( x1 Int )( x2 Int )( x3 Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( d1 Int )( d2 Int )( d3 Int )( x1 Int )( x2 Int )( x3 Int )( d1_0 Int )( d2_0 Int )( d3_0 Int )( x1_0 Int )( x1_1 Int )( x1_2 Int )( x1_3 Int )( x2_0 Int )( x2_1 Int )( x2_2 Int )( x2_3 Int )( x3_0 Int )( x3_1 Int )( x3_2 Int )( x3_3 Int ) ) Bool
	( and
		( = d1 d1_0 )
		( = d2 d2_0 )
		( = d3 d3_0 )
		( = x1 x1_0 )
		( = d1_0 1 )
		( = d2_0 1 )
		( = d3_0 1 )
		( = x1_0 1 )
	)
)

( define-fun trans-f ( ( d1 Int )( d2 Int )( d3 Int )( x1 Int )( x2 Int )( x3 Int )( d1! Int )( d2! Int )( d3! Int )( x1! Int )( x2! Int )( x3! Int )( d1_0 Int )( d2_0 Int )( d3_0 Int )( x1_0 Int )( x1_1 Int )( x1_2 Int )( x1_3 Int )( x2_0 Int )( x2_1 Int )( x2_2 Int )( x2_3 Int )( x3_0 Int )( x3_1 Int )( x3_2 Int )( x3_3 Int ) ) Bool
	( or
		( and
			( = x1_1 x1 )
			( = x2_1 x2 )
			( = x3_1 x3 )
			( = x1_1 x1! )
			( = x2_1 x2! )
			( = x3_1 x3! )
			( = d1 d1! )
			( = d2 d2! )
			( = d3 d3! )
			( = x2 x2! )
			( = x3 x3! )
		)
		( and
			( = x1_1 x1 )
			( = x2_1 x2 )
			( = x3_1 x3 )
			( > x1_1 0 )
			( > x2_1 0 )
			( > x3_1 0 )
			( = x1_2 ( - x1_1 d1_0 ) )
			( = x2_2 ( - x2_1 d2_0 ) )
			( = x3_2 ( - x3_1 d3_0 ) )
			( = x1_3 x1_2 )
			( = x2_3 x2_2 )
			( = x3_3 x3_2 )
			( = x1_3 x1! )
			( = x2_3 x2! )
			( = x3_3 x3! )
			(= d1 d1_0 )
			(= d1! d1_0 )
			(= d2 d2_0 )
			(= d2! d2_0 )
			(= d3 d3_0 )
			(= d3! d3_0 )
		)
		( and
			( = x1_1 x1 )
			( = x2_1 x2 )
			( = x3_1 x3 )
			( > x1_1 0 )
			( > x2_1 0 )
			( not ( > x3_1 0 ) )
			( = x1_3 x1_1 )
			( = x2_3 x2_1 )
			( = x3_3 x3_1 )
			( = x1_3 x1! )
			( = x2_3 x2! )
			( = x3_3 x3! )
			(= d1 d1_0 )
			(= d1! d1_0 )
			(= d2 d2_0 )
			(= d2! d2_0 )
			(= d3 d3_0 )
			(= d3! d3_0 )
		)
		( and
			( = x1_1 x1 )
			( = x2_1 x2 )
			( = x3_1 x3 )
			( > x1_1 0 )
			( not ( > x2_1 0 ) )
			( = x1_3 x1_1 )
			( = x2_3 x2_1 )
			( = x3_3 x3_1 )
			( = x1_3 x1! )
			( = x2_3 x2! )
			( = x3_3 x3! )
			(= d1 d1_0 )
			(= d1! d1_0 )
			(= d2 d2_0 )
			(= d2! d2_0 )
			(= d3 d3_0 )
			(= d3! d3_0 )
		)
	)
)

( define-fun post-f ( ( d1 Int )( d2 Int )( d3 Int )( x1 Int )( x2 Int )( x3 Int )( d1_0 Int )( d2_0 Int )( d3_0 Int )( x1_0 Int )( x1_1 Int )( x1_2 Int )( x1_3 Int )( x2_0 Int )( x2_1 Int )( x2_2 Int )( x2_3 Int )( x3_0 Int )( x3_1 Int )( x3_2 Int )( x3_3 Int ) ) Bool
	( or
		( not
			( and
				( = d1 d1_0)
				( = d2 d2_0)
				( = d3 d3_0)
				( = x1 x1_1)
				( = x2 x2_1)
				( = x3 x3_1)
			)
		)
		( not
			( and
				( not ( > x1_1 0 ) )
				( not ( >= x3_1 0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f d1 d2 d3 x1 x2 x3 d1_0 d2_0 d3_0 x1_0 x1_1 x1_2 x1_3 x2_0 x2_1 x2_2 x2_3 x3_0 x3_1 x3_2 x3_3  )
		( inv-f d1 d2 d3 x1 x2 x3 )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f d1 d2 d3 x1 x2 x3 )
			( trans-f d1 d2 d3 x1 x2 x3 d1! d2! d3! x1! x2! x3! d1_0 d2_0 d3_0 x1_0 x1_1 x1_2 x1_3 x2_0 x2_1 x2_2 x2_3 x3_0 x3_1 x3_2 x3_3 )
		)
		( inv-f d1! d2! d3! x1! x2! x3! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f d1 d2 d3 x1 x2 x3  )
		( post-f d1 d2 d3 x1 x2 x3 d1_0 d2_0 d3_0 x1_0 x1_1 x1_2 x1_3 x2_0 x2_1 x2_2 x2_3 x3_0 x3_1 x3_2 x3_3 )
	)
))

