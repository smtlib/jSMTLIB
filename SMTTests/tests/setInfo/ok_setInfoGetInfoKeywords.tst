; set-info accepts any attribute, including get-info keywords, and does not change what get-info reports
(set-info :name "x")
(get-info :name)
(set-info :authors "x")
(get-info :authors)
(set-info :version "0")
(get-info :version)
(set-info :error-behavior x)
(get-info :error-behavior)
