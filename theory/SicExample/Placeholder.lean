module

/-!
# Placeholder

The library `SicExample` holds the examples of the RFCs and of the literature, as `CONTRIBUTING.md`
says. It has no example yet: the core alone has no type of data, so its examples would show little,
and they wait for the records, the codata and the observational equality. This module only keeps
the library built and checked, since the checker of Lean refuses a library without a module; the
first example replaces it.
-/

@[expose] public section

namespace SicExample

example : True := trivial

end SicExample
