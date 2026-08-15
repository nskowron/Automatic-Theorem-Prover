echo "Trying to prove propositions from test:"

if output=$(cabal build lib:test 2>&1 >/dev/null); then
    echo -e "\n\033[32mAll tests passed.\033[0m"
else
    echo -e "\n\033[31mFailed testcases:\033[0m"
    echo "$output" | grep " |"
    echo -e "\nRun 'cabal build lib:test' for more info"
fi
