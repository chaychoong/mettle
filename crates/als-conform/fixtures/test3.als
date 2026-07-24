sig A {}

pred impossible {
	some A
	no A
}

run impossible for 3 expect 1
