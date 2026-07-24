sig A {}
sig B {
	r: set A
}

pred show {
	some r
}

run show for 3

assert NoEmpty {
	all b: B | some b.r
}
check NoEmpty for 3
