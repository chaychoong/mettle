#include "../cadical/src/ccadical.cpp"

// This files converts some of the C++ interface of cadical to C.
// These functions are not available in the C interface of cadical.
// The C interface that cadical provides is in: cadical/src/ccadical.h

extern "C"
{
  int ccadical_status(CCaDiCaL *wrapper)
  {
    return ((Wrapper *)wrapper)->solver->status();
  }

  int ccadical_vars(CCaDiCaL *wrapper)
  {
    return ((Wrapper *)wrapper)->solver->vars();
  }

  const char *ccadical_read_dimacs(CCaDiCaL *wrapper, const char *path,
                                   int &vars, int strict)
  {
    return ((Wrapper *)wrapper)->solver->read_dimacs(path, vars, strict);
  }

  const char *ccadical_write_dimacs(CCaDiCaL *wrapper, const char *path,
                                    int min_max_var = 0)
  {
    return ((Wrapper *)wrapper)->solver->write_dimacs(path, min_max_var);
  }

  int ccadical_configure(CCaDiCaL *wrapper, const char *name)
  {
    return ((Wrapper *)wrapper)->solver->configure(name);
  }

  int ccadical_limit2(CCaDiCaL *wrapper,
                      const char *name, int val)
  {
    return ((Wrapper *)wrapper)->solver->limit(name, val);
  }

  void ccadical_reserve(CCaDiCaL *wrapper, int min_max_var = 0)
  {
    ((Wrapper *)wrapper)->solver->reserve(min_max_var);
  }

  // mettle fork (ADR-0027 / mt-121): the search-effort counters, patched into
  // the vendored CaDiCaL as 'Solver::conflicts/decisions/propagations'.
  int64_t ccadical_conflicts(CCaDiCaL *wrapper)
  {
    return ((Wrapper *)wrapper)->solver->conflicts();
  }

  int64_t ccadical_decisions(CCaDiCaL *wrapper)
  {
    return ((Wrapper *)wrapper)->solver->decisions();
  }

  int64_t ccadical_propagations(CCaDiCaL *wrapper)
  {
    return ((Wrapper *)wrapper)->solver->propagations();
  }

  // mettle fork (ADR-0027 / mt-121): DRAT proof tracing. CaDiCaL's own C API
  // reaches this through 'ccadical_trace_proof(wrapper, FILE *, name)', which
  // makes the caller own the stream; the path-only C++ overload lets CaDiCaL
  // open and close the file itself, which is the only form a Rust caller can
  // use without an FFI stdio dependency. Hence the distinct name -- the
  // upstream symbol is already defined in the file this one includes, so it
  // cannot be reused for a different signature.
  //
  // Returns 1 when the trace file was opened, 0 when it was not. Must be called
  // in the CONFIGURING state -- before the first clause AND before
  // 'ccadical_reserve', both of which leave that state; CaDiCaL's contract check
  // aborts the process otherwise.
  int ccadical_trace_proof_path(CCaDiCaL *wrapper, const char *path)
  {
    return ((Wrapper *)wrapper)->solver->trace_proof(path) ? 1 : 0;
  }

  // Flushes buffered proof lines to the trace file. CaDiCaL requires an open
  // trace here (it aborts on a solver that is not tracing, or whose trace is
  // already closed); closing is 'ccadical_close_proof', which the included
  // upstream C API already provides.
  void ccadical_flush_proof(CCaDiCaL *wrapper)
  {
    ((Wrapper *)wrapper)->solver->flush_proof_trace();
  }
}
