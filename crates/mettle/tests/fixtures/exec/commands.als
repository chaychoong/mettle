sig A {}
pred p { some A }
assert AlwaysTrue { some A implies some A }
assert Bogus { no A }
run p for 2 expect 1
check AlwaysTrue for 2 expect 0
check Bogus for 2
check Bogus for 2 expect 0
