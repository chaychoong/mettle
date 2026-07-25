// mt-062: overflow in eval position wraps silently, with no marker (E-31).
sig A {}

run Show { some A } for 3 but 4 int
