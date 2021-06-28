//! Types for the *m.room.topic* event.

use ruma_events_macros::EventContent;
use serde::{Deserialize, Serialize};

use crate::StateEvent;

/// A topic is a short message detailing what is currently being discussed in the room.
pub type TopicEvent = StateEvent<TopicEventContent>;

/// The payload for `TopicEvent`.
#[derive(Clone, Debug, Deserialize, Serialize, EventContent)]
#[cfg_attr(not(feature = "unstable-exhaustive-types"), non_exhaustive)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[ruma_event(type = "m.room.topic", kind = State)]
pub struct TopicEventContent {
    /// The topic text.
    pub topic: String,
}

impl TopicEventContent {
    /// Creates a new `TopicEventContent` with the given topic.
    pub fn new(topic: String) -> Self {
        Self { topic }
    }
}
