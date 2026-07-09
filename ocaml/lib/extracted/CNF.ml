
type polarity =
| Coq_pos
| Coq_neg

type 'v literal = 'v * polarity

type 'v clause = 'v literal list

type 'v cnf = 'v clause list

type 'v assignment = 'v -> bool
