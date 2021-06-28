//! Helper module for the Serialize / Deserialize impl's for the User struct
//! in the parent module.

use ruma_common::thirdparty::Medium;
use ruma_serde::Outgoing;
use serde::Serialize;

// The following structs could just be used in place of the one in the parent module, but
// that one is arguably much easier to deal with.
#[derive(Clone, Debug, PartialEq, Eq, Outgoing, Serialize)]
#[serde(tag = "type")]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub(crate) enum UserIdentifier<'a> {
    #[serde(rename = "m.id.user")]
    MatrixId { user: &'a str },
    #[serde(rename = "m.id.thirdparty")]
    ThirdPartyId { medium: Medium, address: &'a str },
    #[serde(rename = "m.id.phone")]
    PhoneNumber { country: &'a str, phone: &'a str },
}

impl<'a> From<super::UserIdentifier<'a>> for UserIdentifier<'a> {
    fn from(id: super::UserIdentifier<'a>) -> Self {
        use super::UserIdentifier as SuperId;
        use UserIdentifier as SerdeId;

        match id {
            SuperId::MatrixId(user) => SerdeId::MatrixId { user },
            SuperId::ThirdPartyId { address, medium } => SerdeId::ThirdPartyId { address, medium },
            SuperId::PhoneNumber { country, phone } => SerdeId::PhoneNumber { country, phone },
        }
    }
}

impl From<IncomingUserIdentifier> for super::IncomingUserIdentifier {
    fn from(id: IncomingUserIdentifier) -> super::IncomingUserIdentifier {
        use super::IncomingUserIdentifier as SuperId;
        use IncomingUserIdentifier as SerdeId;

        match id {
            SerdeId::MatrixId { user } => SuperId::MatrixId(user),
            SerdeId::ThirdPartyId { address, medium } => SuperId::ThirdPartyId { address, medium },
            SerdeId::PhoneNumber { country, phone } => SuperId::PhoneNumber { country, phone },
        }
    }
}
