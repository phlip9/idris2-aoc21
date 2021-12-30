#!/bin/bash

set -e

function usage() {
    echo "x [option ...] subcommand"
    echo ""
    echo "· x run - run the main package binary"
    echo "· x check - typecheck the main package"
    echo "· x repl - start an idris2 repl on the main package"
    echo "· x test - run all tests"
    echo "· x test-repl - start an idris2 repl on the test package"
}

case "$1" in 
    run)
        nix run .#aoc21
        ;;
    check)
        nix develop -c idris2 -Werror --typecheck aoc21.ipkg
        # nix develop .#tests -c idris2 -Werror --typecheck test.ipkg
        ;;
    repl)
        nix develop -c rlwrap idris2 --repl aoc21.ipkg
        ;;
    test)
        nix run .#tests
        ;;
    test-repl)
        nix develop .#tests -c rlwrap idris2 --repl test.ipkg
        ;;
    *) usage
        ;;
esac
