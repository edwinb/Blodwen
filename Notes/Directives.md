# Compiler Directives

There are a number of directives (instructions to the compiler, beginning with
a `%` symbol) which are not part of the Idris 2 language, but nevertheless
provide useful information to the compiler. Mostly these will be useful for
library (especially Prelude) authors. They are ordered here approximately
by "likelihood of being useful to most programmers".

## Language directives

### %name

Syntax: `%name <name> <name_list>`

For interactive editing purposes, use `<name_list>` as the preferred names
for variables with type `<name>`.

### %hide

Syntax: `%hide <name>`

Throughout the rest of the file, consider the `<name>` to be private to its
own namespace.

### %auto_lazy

Syntax: `%auto_lazy <on | off>`

Turn the automatic insertion of laziness annotations on or off. Default is
`on` as long as `%lazy` names have been defined (see below).

### %runElab

Syntax: `%runElab <expr>`

Run the elaborator reflection expression `<expr>`, which must be of type
`Elab a`. Note that this is only minimally implemented at the moment.

### %hide_export

Syntax: `%hide <name>`

Throughout the rest of the file *and any file which imports this module*, 
consider the `<name>` to be private to its own namespace.

### %lazy

Syntax: `%lazy <lazy_name> <delay_name> <force_name>`

Use the given names for implicit insertion of laziness annotations.

### %pair

Syntax: `%pair <pair_type> <fst_name> <snd_name>`

Use the given names in `auto` implicit search for projecting from pair types.

### %rewrite

Syntax: `%rewrite <rewrite_name>`

Use the given name as the default rewriting function in the `rewrite` syntax.

### %integerLit

Syntax: `%integerLit <fromInteger_name>`

Apply all integer literals to the given function name when elaborating.
The default Prelude sets this to `fromInteger`.

### %stringLit

Apply all string literals to the given function name when elaborating.
The default Prelude does not set this.

### %charLit

Apply all character literals to the given function name when elaborating.
The default Prelude does not set this.

## Implementation/debugging directives

### %logging

Syntax: `%logging <level>`

Set the logging level. In general `1` tells you which top level declaration
the elaborator is working on, up to `5` gives you more specific details of
each stage of the elaboration, and up to `10` gives you full details of
type checking including progress on unification problems

