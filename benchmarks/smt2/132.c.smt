(set-logic LIA)

( declare-const c Int )
( declare-const c! Int )
( declare-const i Int )
( declare-const i! Int )
( declare-const j Int )
( declare-const j! Int )
( declare-const t Int )
( declare-const t! Int )
( declare-const tmp Int )
( declare-const tmp! Int )

( declare-const c_0 Int )
( declare-const i_0 Int )
( declare-const i_1 Int )
( declare-const i_2 Int )
( declare-const i_3 Int )
( declare-const j_0 Int )
( declare-const j_1 Int )
( declare-const j_2 Int )
( declare-const j_3 Int )
( declare-const t_0 Int )
( declare-const t_1 Int )
( declare-const t_2 Int )
( declare-const t_3 Int )

( define-fun inv-f( ( c Int )( i Int )( j Int )( t Int )( tmp Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( c Int )( i Int )( j Int )( t Int )( tmp Int )( c_0 Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( t_0 Int )( t_1 Int )( t_2 Int )( t_3 Int ) ) Bool
	( and
		( = i i_0 )
		( = i_0 0 )
	)
)

( define-fun trans-f ( ( c Int )( i Int )( j Int )( t Int )( tmp Int )( c! Int )( i! Int )( j! Int )( t! Int )( tmp! Int )( c_0 Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( t_0 Int )( t_1 Int )( t_2 Int )( t_3 Int ) ) Bool
	( or
		( and
			( = i_1 i )
			( = j_1 j )
			( = t_1 t )
			( = i_1 i! )
			( = j_1 j! )
			( = t_1 t! )
			( = c c! )
			( = i i! )
			( = j j! )
			( = t t! )
			(= tmp tmp! )
		)
		( and
			( = i_1 i )
			( = j_1 j )
			( = t_1 t )
			( > c_0 48 )
			( < c_0 57 )
			( = j_2 ( + i_1 i_1 ) )
			( = t_2 ( - c_0 48 ) )
			( = i_2 ( + j_2 t_2 ) )
			( = i_3 i_2 )
			( = j_3 j_2 )
			( = t_3 t_2 )
			( = i_3 i! )
			( = j_3 j! )
			( = t_3 t! )
			(= c c_0 )
			(= c! c_0 )
			(= tmp tmp! )
		)
		( and
			( = i_1 i )
			( = j_1 j )
			( = t_1 t )
			( > c_0 48 )
			( not ( < c_0 57 ) )
			( = i_3 i_1 )
			( = j_3 j_1 )
			( = t_3 t_1 )
			( = i_3 i! )
			( = j_3 j! )
			( = t_3 t! )
			(= c c_0 )
			(= c! c_0 )
			(= tmp tmp! )
		)
		( and
			( = i_1 i )
			( = j_1 j )
			( = t_1 t )
			( not ( > c_0 48 ) )
			( = i_3 i_1 )
			( = j_3 j_1 )
			( = t_3 t_1 )
			( = i_3 i! )
			( = j_3 j! )
			( = t_3 t! )
			(= c c_0 )
			(= c! c_0 )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( c Int )( i Int )( j Int )( t Int )( tmp Int )( c_0 Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( t_0 Int )( t_1 Int )( t_2 Int )( t_3 Int ) ) Bool
	( or
		( not
			( and
				( = c c_0 )
				( = i i_1)
				( = j j_1)
				( = t t_1)
			)
		)
		( not
			( and
				( not ( >= i_1 0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f c i j t tmp c_0 i_0 i_1 i_2 i_3 j_0 j_1 j_2 j_3 t_0 t_1 t_2 t_3  )
		( inv-f c i j t tmp )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f c i j t tmp )
			( trans-f c i j t tmp c! i! j! t! tmp! c_0 i_0 i_1 i_2 i_3 j_0 j_1 j_2 j_3 t_0 t_1 t_2 t_3 )
		)
		( inv-f c! i! j! t! tmp! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f c i j t tmp  )
		( post-f c i j t tmp c_0 i_0 i_1 i_2 i_3 j_0 j_1 j_2 j_3 t_0 t_1 t_2 t_3 )
	)
))

