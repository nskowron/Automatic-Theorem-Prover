echo "Testing Provable:"

ghc -fno-code -i./../src Provable.hs 2>&1 | grep prove

# if ghc -fno-code Unprovable.hs >/dev/null 2>&1; then
#     echo "Unprovable Failed"
# else
#     echo "Unprovable Passed"
# fi
