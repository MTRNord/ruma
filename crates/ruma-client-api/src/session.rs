//! Endpoints for user session management.

pub mod get_login_types;
pub mod login;
pub mod login_fallback;
pub mod logout;
pub mod logout_all;
#[cfg(feature = "unstable-msc2918")]
pub mod refresh_token;
pub mod sso_login;
pub mod sso_login_with_provider;
