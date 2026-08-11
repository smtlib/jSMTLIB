; Tests the :reproducible-resource-limit option: default 0, and a set/get round trip.
(get-option :reproducible-resource-limit)
(set-option :reproducible-resource-limit 5)
(get-option :reproducible-resource-limit)
(set-option :reproducible-resource-limit 0)
(get-option :reproducible-resource-limit)
