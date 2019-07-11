macro_rules! slice_to_array {
    ($slice:expr, $len:expr) => {
        {
            let mut array = [0; $len];
            array.copy_from_slice($slice); 
            array
        }
    };
}

macro_rules! zero_padding {
    ($vec:expr, $n:expr) => {
        {
            for _ in 0..$n {
                $vec.push(0u8);
            }
        }
    };
}

macro_rules! remove_zero_padding {
    ($vec:expr) => {
        {
            while $vec.last() == Some(&0u8) {
                $vec.pop();
            }
        }
    };
}