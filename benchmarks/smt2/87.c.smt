(set-logic LIA)

( declare-const lock Int )
( declare-const lock! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const lock_0 Int )
( declare-const lock_1 Int )
( declare-const lock_2 Int )
( declare-const lock_3 Int )
( declare-const lock_4 Int )
( declare-const lock_5 Int )
( declare-const x_0 Int )
( declare-const x_1 Int )
( declare-const x_2 Int )
( declare-const x_3 Int )
( declare-const x_4 Int )
( declare-const x_5 Int )
( declare-const y_0 Int )
( declare-const y_1 Int )
( declare-const y_2 Int )
( declare-const y_3 Int )

( define-fun inv-f( ( lock Int )( x Int )( y Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( and
		( = lock lock_1 )
		( = x x_1 )
		( = y y_0 )
		( = x_1 y_0 )
		( = lock_1 1 )
	)
)

( define-fun trans-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock! Int )( x! Int )( y! Int )( tmp! Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( or
		( and
			( = lock_2 lock )
			( = x_2 x )
			( = y_1 y )
			( = lock_2 lock! )
			( = x_2 x! )
			( = y_1 y! )
			( = lock lock! )
			(= tmp tmp! )
		)
		( and
			( = lock_2 lock )
			( = x_2 x )
			( = y_1 y )
			( not ( = x_2 y_1 ) )
			( = lock_3 1 )
			( = x_3 y_1 )
			( = lock_4 lock_3 )
			( = x_4 x_3 )
			( = y_2 y_1 )
			( = lock_4 lock! )
			( = x_4 x! )
			( = y_2 y! )
			(= tmp tmp! )
		)
		( and
			( = lock_2 lock )
			( = x_2 x )
			( = y_1 y )
			( not ( = x_2 y_1 ) )
			( = lock_5 0 )
			( = x_5 y_1 )
			( = y_3 ( + y_1 1 ) )
			( = lock_4 lock_5 )
			( = x_4 x_5 )
			( = y_2 y_3 )
			( = lock_4 lock! )
			( = x_4 x! )
			( = y_2 y! )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( or
		( not
			( and
				( = lock lock_2)
				( = x x_2)
				( = y y_1)
			)
		)
		( not
			( and
				( not ( not ( = x_2 y_1 ) ) )
				( not ( = lock_2 1 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f lock x y tmp lock_0 lock_1 lock_2 lock_3 lock_4 lock_5 x_0 x_1 x_2 x_3 x_4 x_5 y_0 y_1 y_2 y_3  )
		( inv-f lock x y tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f lock x y tmp )
			( trans-f lock x y tmp lock! x! y! tmp! lock_0 lock_1 lock_2 lock_3 lock_4 lock_5 x_0 x_1 x_2 x_3 x_4 x_5 y_0 y_1 y_2 y_3 )
		)
		( inv-f lock! x! y! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f lock x y tmp  )
		( post-f lock x y tmp lock_0 lock_1 lock_2 lock_3 lock_4 lock_5 x_0 x_1 x_2 x_3 x_4 x_5 y_0 y_1 y_2 y_3 )
	)
))

