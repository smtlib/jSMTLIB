; Semicolons and parentheses inside strings and quoted symbols are not comments or structure
(set-info :source "a string ; not a comment (nor a list)")
(declare-fun |a ; b (c)| () Bool)
(declare-fun |multi
line| () Bool)
(assert (or |a ; b (c)| |multi
line|)) ; after a multi-line symbol
(echo "two
lines ""quoted""") ; non-ASCII: é π 字
(declare-fun |π| () Bool)
