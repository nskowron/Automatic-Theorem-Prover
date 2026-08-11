echo "Trying to prove propositions from Provable.hs:"

if output=$(ghc -fno-code -i./../src Provable.hs 2>&1 >/dev/null); then
    echo -e "\n\033[32mAll tests passed.\033[0m"
else
    echo -e "\n\033[31mFailed testcases:\033[0m"
    echo "$output" | grep " |"
    echo -e "\nRun 'ghc -fno-code -i./../src Provable.hs' for more info"
fi
