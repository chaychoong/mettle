-- mt-072 serve fixture: two commands, so `serve` must be told which one.
sig A {}
pred p { some A }
pred q { no A }
run p for 2
run q for 2
