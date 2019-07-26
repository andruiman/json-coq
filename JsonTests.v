
(*
DO_SMTH BY_METHOD WITH_PARAM AT_PATH
json2 -> json3

REMOVE (by purge) "type" AT ".*" -- all rooted collection


-- {"name" # '[{"given" # '[$"Andy"; $"Michael"], "family" # $"Watson"};
               {"given" # '[$"Andrey"], "family" # $"Watsonov"}]}

DESTRUCT (by disjoin, indexate) AT ".*.name"  -- on lists
-- "name1" # {"given" # '[$"Andy"; $"Michael"], "family" # $"Watson"}
-- "name2" # {"given" # '[$"Andrey"], "family" # $"Watsonov"}

DESTRUCT (by renaming, indexate key???) AT ".*.name*" -- on maps
-- {"given1" # '[$"Andy"; $"Michael"], "family1" # $"Watson",
--  "given2" # '[$"Andrey"], "family2" # $"Watsonov"}

DESTRUCT (by concat, with delimiter " ") AT ".*.given*" -- on  lists
-- {"given1" # $"Andy Michael"], "family1" # $"Watson",
--  "given2" # $"Andrey", "family2" # $"Watsonov"}

-- {"telecom" # '[{"system" # $"phone", "value" # $"1234"};
--                {"system" # $"phone", "value" # $"5678"};
--                {"system" # $"mail", "value" # $"andy@watson.me"};
--                {"system" # $"mail", "value" # $"andrey@mail.ru"}]}

DESTRUCT (by disjoin, indexate) AT ".*.telecom" -- on lists
-- {"telecom1" # {"system" # $"phone", "value" # $"1234"},
--  "telecom2" # {"system" # $"phone", "value" # $"5678"},
--  "telecom3" # {"system" # $"mail", "value" # $"andy@watson.me"},
--  "telecom4" # {"system" # $"mail", "value" # $"andrey@mail.ru"}}

SET (by replace with map {@"system" # @"value"}) AT ".*.telecom*" -- on maps
-- {"telecom1" # {"phone" # $"1234"},
--  "telecom2" # {"phone" # $"5678"},
--  "telecom3" # {"mail"  # $"andy@watson.me"},
--  "telecom4" # {"mail"  # $"andrey@mail.ru"}}

DESTRUCT (by renaming, indexate key???) AT ".*.telecom*" -- on maps
-- {"phone1" # $"1234",
--  "phone2" # $"5678",
--  "mail1"  # $"andy@watson.me",
--  "mail2"  # $"andrey@mail.ru"}

*)

(*
json3 -> json2
-- {"phone1" # $"1234", "phone2" # $"5678",
--  "mail1" # $"andy@watson.me",
--  "mail2" # $"andrey@mail.ru"}

SET (by destruct_insert of values ".*.phone*") AT ".*.phones"
SET (by destruct_insert of values ".*.mail*") AT ".*.mails"
-- {"phones" # '[$"1234"; $"5678"],
--  "mails"  # '[$"andy@watson.me"; $"andrey@mail.ru"]}

SET (by replace with map {"system" # $"phone", "value" # @id}) AT ".*.phones.*"
SET (by replace with map {"system" # $"mail", "value" # @id}) AT ".*.mails.*"
-- {"phones" # '[{"system" # $"phone", "value" # $"1234"}; 
--               {"system" # $"phone", "value" # $"5678"}],
--  "mails"  # '[{"system" # $"mail", "value"$"andy@watson.me"}; 
--               {"system" # $"mail", "value"$"andrey@mail.ru"}]}

SET (by destruct_insert of values [".*.mails", ".*.phones"]) AT ".*.telecom"
-- {"telecom" # '['[{"system" # $"phone", "value" # $"1234"}; 
--               {"system" # $"phone", "value" # $"5678"}];
--              '[{"system" # $"mail", "value"$"andy@watson.me"}; 
--               {"system" # $"mail", "value"$"andrey@mail.ru"}]]}

SET (by replace with map flatten) AT ".*.telecom"
-- {"telecom" # '[{"system" # $"phone", "value" # $"1234"}; 
--               {"system" # $"phone", "value" # $"5678"};
--               {"system" # $"mail", "value"$"andy@watson.me"}; 
--               {"system" # $"mail", "value"$"andrey@mail.ru"}]}
*)