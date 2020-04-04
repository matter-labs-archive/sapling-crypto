
struct CosetCombiner<E: Engine> {
    domain_size: usize,
    log_domain_size: usize,
    wrapping_factor: usize,
    _marker: std::marker::PhantomData<E>,
}


impl<E: Engine> CosetCombiner<E> {

    pub fn new(domain_size: usize, wrapping_factor: usize) -> Self {
        assert!(size.is_power_of_two());
        let height = Self::log2_floor(size);

        CosetCombiner {

        }
    }

    pub fn n
}
