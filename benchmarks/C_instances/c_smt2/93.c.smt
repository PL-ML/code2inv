(set-logic LIA)

( declare-const i Int )
( declare-const i! Int )
( declare-const n Int )
( declare-const n! Int )
( declare-const x Int )
( declare-const x! Int )
( declare-const y Int )
( declare-const y! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const i_0 Int )
( declare-const i_1 Int )
( declare-const i_2 Int )
( declare-const i_3 Int )
( declare-const n_0 Int )
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
( declare-const y_4 Int )
( declare-const y_5 Int )

( define-fun inv-f( ( i Int )( n Int )( x Int )( y Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( i Int )( n Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int )( y_5 Int ) ) Bool
	( and
		( = i i_1 )
		( = n n_0 )
		( = x x_1 )
		( = y y_1 )
		( >= n_0 0 )
		( = i_1 0 )
		( = x_1 0 )
		( = y_1 0 )
	)
)

( define-fun trans-f ( ( i Int )( n Int )( x Int )( y Int )( tmp Int )( i! Int )( n! Int )( x! Int )( y! Int )( tmp! Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int )( y_5 Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = x_2 x )
			( = y_2 y )
			( = i_2 i! )
			( = x_2 x! )
			( = y_2 y! )
			( = n n_0 )
			( = n! n_0 )
			( = x x! )
			( = y y! )
			(= tmp tmp! )
		)
		( and
			( = i_2 i )
			( = x_2 x )
			( = y_2 y )
			( < i_2 n_0 )
			( = i_3 ( + i_2 1 ) )
			( = x_3 ( + x_2 1 ) )
			( = y_3 ( + y_2 2 ) )
			( = x_4 x_3 )
			( = y_4 y_3 )
			( = i_3 i! )
			( = x_4 x! )
			( = y_4 y! )
			(= n n_0 )
			(= n! n_0 )
			(= tmp tmp! )
		)
		( and
			( = i_2 i )
			( = x_2 x )
			( = y_2 y )
			( < i_2 n_0 )
			( = i_3 ( + i_2 1 ) )
			( = x_5 ( + x_2 2 ) )
			( = y_5 ( + y_2 1 ) )
			( = x_4 x_5 )
			( = y_4 y_5 )
			( = i_3 i! )
			( = x_4 x! )
			( = y_4 y! )
			(= n n_0 )
			(= n! n_0 )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( i Int )( n Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int )( y_5 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = n n_0)
				( = x x_2)
				( = y y_2)
			)
		)
		( not
			( and
				( not ( < i_2 n_0 ) )
				( not ( = ( * 3 n_0 ) ( + x_2 y_2 ) ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f i n x y tmp i_0 i_1 i_2 i_3 n_0 x_0 x_1 x_2 x_3 x_4 x_5 y_0 y_1 y_2 y_3 y_4 y_5  )
		( inv-f i n x y tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f i n x y tmp )
			( trans-f i n x y tmp i! n! x! y! tmp! i_0 i_1 i_2 i_3 n_0 x_0 x_1 x_2 x_3 x_4 x_5 y_0 y_1 y_2 y_3 y_4 y_5 )
		)
		( inv-f i! n! x! y! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f i n x y tmp  )
		( post-f i n x y tmp i_0 i_1 i_2 i_3 n_0 x_0 x_1 x_2 x_3 x_4 x_5 y_0 y_1 y_2 y_3 y_4 y_5 )
	)
))

