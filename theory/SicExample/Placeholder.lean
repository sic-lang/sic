module

/-!
# Placeholder

The library `SicExample` holds the examples of the RFCs and of the literature, as `CONTRIBUTING.md`
says. It has no example yet: the examples wait until the formalization proves every claim of the
RFCs, to be written then, all at once. This module only keeps the library built and checked, since
the checker of Lean refuses a library without a module; the first example replaces it.
-/

@[expose] public section

namespace SicExample

example : True := trivial

end SicExample
