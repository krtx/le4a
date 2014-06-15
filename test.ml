
open OUnit

let _ =
  run_test_tt_main
    ("Test ML" >::: [Test_eval.suite; Test_typing.suite;])
