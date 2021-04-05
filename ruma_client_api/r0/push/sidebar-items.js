initSidebarItems({"enum":[["PusherKind","Which kind a pusher is."],["RuleKind","The kinds of push rules that are available."]],"mod":[["delete_pushrule","DELETE /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}"],["get_notifications","GET /_matrix/client/r0/notifications"],["get_pushers","GET /_matrix/client/r0/pushers"],["get_pushrule","GET /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}"],["get_pushrule_actions","GET /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}/actions"],["get_pushrule_enabled","GET /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}/enabled"],["get_pushrules_all","GET /_matrix/client/r0/pushrules/"],["get_pushrules_global_scope","GET /_matrix/client/r0/pushrules/global/"],["set_pusher","POST /_matrix/client/r0/pushers/set"],["set_pushrule","PUT /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}"],["set_pushrule_actions","PUT /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}/actions"],["set_pushrule_enabled","PUT /_matrix/client/r0/pushrules/{scope}/{kind}/{ruleId}/enabled"]],"struct":[["MissingConditionsError","An error that happens when `PushRule` cannot be converted into `ConditionalPushRule`"],["MissingPatternError","An error that happens when `PushRule` cannot be converted into `PatternedPushRule`"],["PushRule","Like `SimplePushRule`, but may represent any kind of push rule thanks to `pattern` and `conditions` being optional."],["Pusher","Defines a pusher."]]});