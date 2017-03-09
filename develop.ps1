
$test = if ($args[1]) {$args[1]} else {"Spec.main"}
$main = "simple-frp:test:simple-frp-test"
ghcid --command="stack repl --test --main-is=$main" --test=$test