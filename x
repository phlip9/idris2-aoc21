#!/bin/bash

set -e

function usage() {
    echo "x [option ...] subcommand"
    echo ""
    echo "· x run - run the main package binary"
    echo "· x run-prof - run the main package with profiling enabled"
    echo "· x check - typecheck the main package"
    echo "· x repl - start an idris2 repl on the main package"
    echo "· x test - run all tests"
    echo "· x test-check - typecheck the tests"
    echo "· x test-repl - start an idris2 repl on the test package"
}

case "$1" in 
    run)
        shift
        nix run .#aoc21 -- $@
        ;;
    run-prof)
        shift
        nix develop -c bash -c "idris2 -Werror --profile --build aoc21.ipkg && build/exec/aoc21 $@"
        ;;
    check)
        nix develop -c idris2 -Werror --typecheck aoc21.ipkg
        ;;
    repl)
        # nix develop -c rlwrap idris2 --repl aoc21.ipkg
        nix develop -c rlwrap idris2 --find-ipkg src/Main.idr
        ;;
    test)
        shift
        HEDGEHOG_COLOR=1 nix run .#tests -- $@
        ;;
    test-check)
        nix develop .#tests -c idris2 -Werror --typecheck test.ipkg
        ;;
    test-repl)
        nix develop .#tests -c rlwrap idris2 --repl test.ipkg
        ;;
    *) usage
        ;;
esac
