-- mt-072 serve fixture: nothing to visualize, so `serve` must refuse loudly
-- rather than open a server onto an empty page.
sig A {}
run { some A and no A } for 2
