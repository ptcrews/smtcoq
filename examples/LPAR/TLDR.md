Assuming you're in a Linux-based system (tested on Ubuntu 20.04),
the following provide a shorter set of 
instructions to execute our artifact.

## 1. Download the solvers from the links and add them to your path:
- [cvc5](https://homepage.divms.uiowa.edu/~viswanathn/lpar23/cvc5-1.0.4.noIte.zip)
- [cvc4](http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt)
- [veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)

## 2. Set up environment for cvc4
In your `.bashrc` (or `.bash_profile`, or any other initialization file read by
your shell), export the following environment variable to make it point at the
`signatures` directory distributed with SMTCoq.

> Don't use `~` in the path but rather `$HOME`.

```bash
export LFSCSIGS="$HOME/path/to/smtcoq/src/lfsc/tests/signatures/"
```

## 3. Install SMTCoq
Assuming [opam](https://opam.ocaml.org) is installed:
```
opam switch create lpar ocaml-base-compiler.4.11.1
opam install coq.8.16.1 coqide.8.16.1
git clone https://github.com/arjunvish/smtcoq.git
cd smtcoq/src/
git checkout lpar23
make
```

## 4. Execute the artifact
Assuming you are in `./src/`:
```
cd ../examples/LPAR/ 
coqide ZorderLpar23.v
```
Now the file can be checked either step-by-step
(Navigation -> forward), or to the end
(Navigation -> Run to end) via CoqIDE. Expected outputs 
are commented after each goal. 