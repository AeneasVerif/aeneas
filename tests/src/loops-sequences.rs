//@ [!lean] skip

struct Key {
    seed: [u8; 32],
    t: [u16; 32],
}

impl Key {
    fn t_mut(&mut self) -> &mut [u16; 32] {
        &mut self.t
    }
}

type HashState = [u8; 8];

fn shake_init(_state: &mut HashState) {}
fn shake_append(_state: &mut HashState, _data: &[u8]) {}
fn shake_state_copy(_src: &HashState, _dst: &mut HashState) {}
fn shake_extract(_src: &HashState, _dst: &mut [u8]) {}

fn sample_cbd(_src: &[u8], _dst: &mut [u16; 32]) {}

fn key_expand(key: &mut Key, state_base: &mut HashState, state_work: &mut HashState) {
    shake_init(state_base);
    shake_append(state_base, &key.seed);

    let mut sample_buffer: [u8; 1] = [0];
    let mut i = 0;
    while i < 32 {
        sample_buffer[0] = i as u8;
        shake_state_copy(state_base, state_work);
        shake_append(state_work, &sample_buffer);
        shake_extract(state_work, &mut sample_buffer);
        sample_cbd(state_work, key.t_mut());
        i += 1;
    }

    let mut i = 0;
    while i < 32 {
        sample_buffer[0] = i as u8;
        shake_state_copy(state_base, state_work);
        shake_append(state_work, &sample_buffer);
        shake_extract(state_work, &mut sample_buffer);
        sample_cbd(state_work, key.t_mut());
        i += 1;
    }
}
