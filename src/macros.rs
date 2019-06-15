macro_rules! slice_to_array {
    ($slice:expr, $len:expr) => {
        {
            let mut array = [0; $len];
            array.copy_from_slice($slice); 
            array
        }
    };
}