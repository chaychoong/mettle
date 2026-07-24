sig A {}

pred impossible {
	some A
	no A
}

run impossible for 3 expect 0

pred possible {
	some A
}

run possible for 3 expect 1

-- deliberately wrong expectation to see how Alloy reports mismatch
run possible for 3 expect 0
