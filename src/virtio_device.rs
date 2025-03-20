#[derive(Default)]
pub struct VirtioDevice {
    pub base_gpa: usize,
    pub length: usize,
}

impl VirtioDevice {
    pub fn new(base_gpa: usize, length: usize) -> Self {
        Self { base_gpa, length }
    }
}
