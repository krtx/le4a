概要
http://www.fos.kuis.kyoto-u.ac.jp/~t-sekiym/classes/isle4/

how to build:
$ ocamlbuild -ocamlc 'ocamlc str.cma' -lflag "-g" -use-menhir -menhir "menhir -v --error-recovery" main.byte
