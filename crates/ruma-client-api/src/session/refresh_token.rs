//! `POST /_matrix/client/*/refresh`
//!
//! Refresh an access token.
//!
//! Clients should use the returned access token when making subsequent API
//! calls, and store the returned refresh token (if given) in order to refresh
//! the new access token when necessary.
//!
//! After an access token has been refreshed, a server can choose to invalidate
//! the old access token immediately, or can choose not to, for example if the
//! access token would expire soon anyways. Clients should not make any
//! assumptions about the old access token still being valid, and should use the
//! newly provided access token instead.
//!
//! The old refresh token remains valid until the new access token or refresh
//! token is used, at which point the old refresh token is revoked.
//!
//! Note that this endpoint does not require authentication via an access token.
//! Authentication is provided via the refresh token.
//!
//! Application Service identity assertion is disabled for this endpoint.

pub mod unstable {
    //! `/unstable/` (MSC2918)
    //!
    //! [MSC2918]: https://github.com/matrix-org/matrix-spec-proposals/pull/2918

    use std::time::Duration;

    use ruma_common::api::ruma_api;

    ruma_api! {
        metadata: {
            description: "Refresh an access token.",
            method: POST,
            name: "refresh",
            unstable_path: "/_matrix/client/unstable/org.matrix.msc2918/refresh",
            rate_limited: true,
            authentication: None,
        }

        request: {
            /// The refresh token.
            pub refresh_token: String,
        }

        response: {
            /// The new access token to use.
            pub access_token: String,

            /// The new refresh token to use when the access token needs to be refreshed again.
            ///
            /// If this is `None`, the old refresh token can be re-used.
            #[serde(skip_serializing_if = "Option::is_none")]
            pub refresh_token: Option<String>,

            /// The lifetime of the access token, in milliseconds.
            ///
            /// If this is `None`, the client can assume that the access token will not expire.
            #[serde(
                with = "ruma_common::serde::duration::opt_ms",
                default,
                skip_serializing_if = "Option::is_none"
            )]
            pub expires_in_ms: Option<Duration>,
        }

        error: crate::Error
    }

    impl Request {
        /// Creates a new `Request` with the given refresh token.
        pub fn new(refresh_token: String) -> Self {
            Self { refresh_token }
        }
    }

    impl Response {
        /// Creates a new `Response` with the given access token.
        pub fn new(access_token: String) -> Self {
            Self { access_token, refresh_token: None, expires_in_ms: None }
        }
    }
}
