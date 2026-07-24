one sig S {
	x: Int,
	y: Int,
	z: Int
}

pred addOverflow {
	S.x = 7
	S.y = 7
	S.z = plus[S.x, S.y]
}

run addOverflow for 3 but 4 int
