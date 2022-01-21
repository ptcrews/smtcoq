type id
type rule
type clause
type params
type args

type step = (id, rule, clause, params, args)
type certif = step list

val remove_notnot : certif -> certif