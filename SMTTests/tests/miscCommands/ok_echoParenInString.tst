; An unbalanced parenthesis inside an echoed string must not stall the reply (#205 item 13)
(echo "a(b")
(echo "x(y)")
(echo "after")
