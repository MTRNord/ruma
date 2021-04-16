initSidebarItems({"derive":[["Outgoing","Derive the `Outgoing` trait, possibly generating an ‘Incoming’ version of the struct this derive macro is used on. Specifically, if no lifetime variables are used on any of the fields of the struct, this simple implementation will be generated:"]],"enum":[["DeviceKeyAlgorithm","The basic key algorithms in the specification."],["EventEncryptionAlgorithm","An encryption algorithm to be used to encrypt messages sent to a room."],["RoomVersionId","A Matrix room version ID."],["SigningKeyAlgorithm","The signing key algorithms defined in the Matrix spec."]],"macro":[["device_id","Shorthand for `Box::<DeviceId>::from`."],["device_key_id","Compile-time checked `DeviceKeyId` construction."],["event_id","Compile-time checked `EventId` construction."],["mxc_uri","Compile-time checked `MxcUri` construction."],["room_alias_id","Compile-time checked `RoomAliasId` construction."],["room_id","Compile-time checked `RoomId` construction."],["room_version_id","Compile-time checked `RoomVersionId` construction."],["server_key_id","Compile-time checked `ServerSigningKeyId` construction."],["server_name","Compile-time checked `ServerName` construction."],["server_signing_key_id","Compile-time checked `ServerSigningKeyId` construction."],["user_id","Compile-time checked `UserId` construction."]],"mod":[["api","(De)serializable types for various Matrix APIs requests and responses and abstractions for them."],["authentication","Common types for authentication."],["directory","Common types for room directory endpoints."],["encryption","Common types for encryption related tasks."],["events","(De)serializable types for the events in the Matrix specification. These types are used by other ruma crates."],["identifiers","Types for Matrix identifiers for devices, events, keys, rooms, servers, users and URIs."],["power_levels","Common types for the `m.room.power_levels` event."],["presence","Common types for the presence module."],["push","Common types for the push notifications module."],["serde","(De)serialization helpers for other ruma crates."],["signatures","Digital signatures according to the Matrix specification."],["thirdparty","Common types for the third party networks module."],["user_id","Matrix user identifiers."]],"struct":[["DeviceId","A Matrix key ID."],["DeviceKeyId","A key algorithm and a device id, combined with a ‘:’."],["EventId","A Matrix event ID."],["KeyId","A key algorithm and key name delimited by a colon"],["KeyName","A Matrix key identifier."],["MxcUri","A URI that should be a Matrix-spec compliant MXC URI."],["RoomAliasId","A Matrix room alias ID."],["RoomId","A Matrix room ID."],["RoomIdOrAliasId","A Matrix room ID or a Matrix room alias ID."],["ServerName","A Matrix-spec compliant server name."],["Signatures","Map of all signatures, grouped by entity"],["UserId","A Matrix user ID."]],"trait":[["Outgoing","A type that can be sent to another party that understands the matrix protocol."]],"type":[["DeviceIdBox","An owned [DeviceId]."],["DeviceSignatures","Map of device signatures for an event, grouped by user."],["DeviceSigningKeyId","Algorithm + key name for device keys."],["EntitySignatures","Map of key identifier to signature values."],["KeyNameBox","An owned [KeyName]."],["ServerNameBox","An owned server name."],["ServerSignatures","Map of server signatures for an event, grouped by server."],["ServerSigningKeyId","Algorithm + key name for homeserver signing keys."]]});