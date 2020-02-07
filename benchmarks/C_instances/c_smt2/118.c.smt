(set-logic LIA)

( declare-const i Int )
( declare-const i! Int )
( declare-const size Int )
( declare-const size! Int )
( declare-const sn Int )
( declare-const sn! Int )

( declare-const i_0 Int )
( declare-const i_1 Int )
( declare-const i_2 Int )
( declare-const i_3 Int )
( declare-const size_0 Int )
( declare-const sn_0 Int )
( declare-const sn_1 Int )
( declare-const sn_2 Int )
( declare-const sn_3 Int )

( define-fun inv-f( ( i Int )( size Int )( sn Int ) ) Bool
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
)

( define-fun pre-f ( ( i Int )( size Int )( sn Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( size_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int ) ) Bool
	( and
		( = i i_1 )
		( = sn sn_1 )
		( = sn_1 0 )
		( = i_1 1 )
	)
)

( define-fun trans-f ( ( i Int )( size Int )( sn Int )( i! Int )( size! Int )( sn! Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( size_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = sn_2 sn )
			( = i_2 i! )
			( = sn_2 sn! )
			( = size size_0 )
			( = size! size_0 )
			( = sn sn! )
		)
		( and
			( = i_2 i )
			( = sn_2 sn )
			( <= i_2 size_0 )
			( = i_3 ( + i_2 1 ) )
			( = sn_3 ( + sn_2 1 ) )
			( = i_3 i! )
			( = sn_3 sn! )
			(= size size_0 )
			(= size! size_0 )
		)
	)
)

( define-fun post-f ( ( i Int )( size Int )( sn Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( size_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = size size_0 )
				( = sn sn_2)
			)
		)
		( not
			( and
				( not ( <= i_2 size_0 ) )
				( not ( = sn_2 size_0 ) )
				( not ( = sn_2 0 ) )
			)
		)
	)
)
SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( pre-f i size sn i_0 i_1 i_2 i_3 size_0 sn_0 sn_1 sn_2 sn_3  )
		( inv-f i size sn )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( and
			( inv-f i size sn )
			( trans-f i size sn i! size! sn! i_0 i_1 i_2 i_3 size_0 sn_0 sn_1 sn_2 sn_3 )
		)
		( inv-f i! size! sn! )
	)
))

SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop
( assert ( not
	( =>
		( inv-f i size sn  )
		( post-f i size sn i_0 i_1 i_2 i_3 size_0 sn_0 sn_1 sn_2 sn_3 )
	)
))

