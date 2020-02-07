(set-logic LIA)

( declare-const c Int )
( declare-const c! Int )
( declare-const n Int )
( declare-const n! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const c_0 Int )
( declare-const c_1 Int )
( declare-const c_2 Int )
( declare-const c_3 Int )
( declare-const c_4 Int )
( declare-const c_5 Int )
( declare-const n_0 Int )

( define-fun inv-f( ( c Int )( n Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( c Int )( n Int )( tmp Int )( c_0 Int )( c_1 Int )( c_2 Int )( c_3 Int )( c_4 Int )( c_5 Int )( n_0 Int ) ) Bool
	( and
		( = c c_1 )
		( = n n_0 )
		( = c_1 0 )
		( > n_0 0 )
	)
)

( define-fun trans-f ( ( c Int )( n Int )( tmp Int )( c! Int )( n! Int )( tmp! Int )( c_0 Int )( c_1 Int )( c_2 Int )( c_3 Int )( c_4 Int )( c_5 Int )( n_0 Int ) ) Bool
	( or
		( and
			( = c_2 c )
			( = c_2 c! )
			( = c c! )
			( = n n! )
			(= tmp tmp! )
		)
		( and
			( = c_2 c )
			( > c_2 n_0 )
			( = c_3 ( + c_2 1 ) )
			( = c_4 c_3 )
			( = c_4 c! )
			(= n n_0 )
			(= n! n_0 )
			(= tmp tmp! )
		)
		( and
			( = c_2 c )
			( not ( > c_2 n_0 ) )
			( = c_4 c_2 )
			( = c_4 c! )
			(= n n_0 )
			(= n! n_0 )
			(= tmp tmp! )
		)
		( and
			( = c_2 c )
			( = c_2 n_0 )
			( = c_5 1 )
			( = c_4 c_5 )
			( = c_4 c! )
			(= n n_0 )
			(= n! n_0 )
			(= tmp tmp! )
		)
		( and
			( = c_2 c )
			( not ( = c_2 n_0 ) )
			( = c_4 c_2 )
			( = c_4 c! )
			(= n n_0 )
			(= n! n_0 )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( c Int )( n Int )( tmp Int )( c_0 Int )( c_1 Int )( c_2 Int )( c_3 Int )( c_4 Int )( c_5 Int )( n_0 Int ) ) Bool
	( or
		( not
			( and
				( = c c_2)
				( = n n_0)
			)
		)
		( not
			( and
				( < c_2 0 )
				( > c_2 n_0 )
				( not ( = c_2 n_0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f c n tmp c_0 c_1 c_2 c_3 c_4 c_5 n_0  )
		( inv-f c n tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f c n tmp )
			( trans-f c n tmp c! n! tmp! c_0 c_1 c_2 c_3 c_4 c_5 n_0 )
		)
		( inv-f c! n! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f c n tmp  )
		( post-f c n tmp c_0 c_1 c_2 c_3 c_4 c_5 n_0 )
	)
))

