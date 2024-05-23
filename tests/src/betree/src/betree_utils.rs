//! The following module implements utilities for [betree.rs].
//! Those utilities are only used for serialization/deserialization (we don't
//! reason about them).
//!
//! The issue is that we can't derive serialization/deserialization
//! implementations directly in betree.rs, otherwise we can't translate.
//! We could have hacked in Aeneas to skip those implementations, but I'd
//! rather put a little bit of engineering time into this file, while thinking
//! about a cleaner way of doing this in general. The following file is not
//! difficult to write and maintain anyway.
#![allow(dead_code)]

use crate::betree::{
    InternalContent, Key, LeafContent, List, Message, NodeId, UpsertFunState, Value,
};
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::vec::Vec;

/// Note that I tried using Serde's facilities to define serialization/
/// deserialization functions for external types, but it proved cumbersome
/// for the betree case.
#[derive(Serialize, Deserialize)]
pub enum UpsertFunStateSerde {
    Add(u64),
    Sub(u64),
}

impl UpsertFunStateSerde {
    fn to_state(self) -> UpsertFunState {
        match self {
            UpsertFunStateSerde::Add(v) => UpsertFunState::Add(v),
            UpsertFunStateSerde::Sub(v) => UpsertFunState::Sub(v),
        }
    }

    fn from_state(msg: UpsertFunState) -> Self {
        match msg {
            UpsertFunState::Add(v) => UpsertFunStateSerde::Add(v),
            UpsertFunState::Sub(v) => UpsertFunStateSerde::Sub(v),
        }
    }
}

/// Same remark as for [UpsertFunStateSerde]
#[derive(Serialize, Deserialize)]
enum MessageSerde {
    Insert(Value),
    Delete,
    Upsert(UpsertFunStateSerde),
}

impl MessageSerde {
    fn to_msg(self) -> Message {
        match self {
            MessageSerde::Insert(v) => Message::Insert(v),
            MessageSerde::Delete => Message::Delete,
            MessageSerde::Upsert(v) => Message::Upsert(v.to_state()),
        }
    }

    fn from_msg(msg: Message) -> Self {
        match msg {
            Message::Insert(v) => MessageSerde::Insert(v),
            Message::Delete => MessageSerde::Delete,
            Message::Upsert(v) => MessageSerde::Upsert(UpsertFunStateSerde::from_state(v)),
        }
    }
}

// For some reason, I don't manage to make that in an impl...
pub(crate) fn list_from_vec<T>(mut v: Vec<T>) -> List<T> {
    // We need to reverse
    v.reverse();
    let mut l = List::Nil;
    for x in v.into_iter() {
        l = List::Cons(x, Box::new(l));
    }
    l
}

// For some reason, I don't manage to make that in an impl...
pub(crate) fn list_to_vec<T>(mut l: List<T>) -> Vec<T> {
    let mut v = Vec::new();
    loop {
        match l {
            List::Nil => break,
            List::Cons(hd, tl) => {
                v.push(hd);
                l = *tl;
            }
        }
    }
    v
}

/// See the equivalent function in betree.rs
pub(crate) fn load_internal_node(id: NodeId) -> InternalContent {
    // Open the file
    std::fs::create_dir_all("tmp").unwrap();
    let filename = format!("tmp/node{}", id).to_string();
    // Read
    let f = File::open(filename).unwrap();
    // Serde makes things easy
    let c: Vec<(Key, MessageSerde)> = serde_json::from_reader(&f).unwrap();
    let c: Vec<(Key, Message)> = c
        .into_iter()
        .map(|(key, msg)| (key, msg.to_msg()))
        .collect();
    // Convert
    list_from_vec(c)
}

/// See the equivalent function in betree.rs
pub(crate) fn store_internal_node(id: NodeId, content: InternalContent) {
    // Open the file
    std::fs::create_dir_all("tmp").unwrap();
    let filename = format!("tmp/node{}", id).to_string();
    // Write
    let f = File::create(filename).unwrap();
    // Convert
    let v: Vec<(Key, Message)> = list_to_vec(content);
    let v: Vec<(Key, MessageSerde)> = v
        .into_iter()
        .map(|(k, msg)| (k, MessageSerde::from_msg(msg)))
        .collect();
    // Serde makes things easy
    serde_json::to_writer(&f, &v).unwrap();
}

/// See the equivalent function in betree.rs
pub(crate) fn load_leaf_node(id: NodeId) -> LeafContent {
    // Open the file
    std::fs::create_dir_all("tmp").unwrap();
    let filename = format!("tmp/node{}", id).to_string();
    // Read
    let f = File::open(filename).unwrap();
    // Serde makes things easy
    let c: Vec<(Key, Value)> = serde_json::from_reader(&f).unwrap();
    // Convert
    list_from_vec(c)
}

/// See the equivalent function in betree.rs
pub(crate) fn store_leaf_node(id: NodeId, content: LeafContent) {
    // Open the file
    std::fs::create_dir_all("tmp").unwrap();
    let filename = format!("tmp/node{}", id).to_string();
    // Write
    let f = File::create(filename).unwrap();
    // Convert
    let v: Vec<(Key, Value)> = list_to_vec(content);
    // Serde makes things easy
    serde_json::to_writer(&f, &v).unwrap();
}
