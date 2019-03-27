pub struct ASWaksman
{
    m_top: Vec<ASWaksman>,
    m_bot: Vec<ASWaksman>,
    m_gate_size: usize,
    m_size: usize,
    m_inputs: Vec<u32>,
    m_outputs: Vec<u32>,
    m_gates: Vec<bool>,
}

impl ASWaksman
{
    fn calculate_gate_size(size: usize) -> usize
    {
        if size == 0 {return 0;}
        if size == 1 {return 0;}
        if size == 2 {return 1;}
        if size == 3 {return 3;}
        if size == 4 {return 5;}

        let is_odd = size % 2 != 0;
        if is_odd == true
        {
            return ASWaksman::calculate_gate_size((size / 2) + 1) + ASWaksman::calculate_gate_size(size / 2) + size - 1;
        }
        return ASWaksman::calculate_gate_size(size / 2) + ASWaksman::calculate_gate_size(size / 2) + size - 1;
    }

    fn set_inputs(&mut self, input: Vec<u32>)
    {
        for i in 0..input.len()
        {
            self.m_inputs[i] = input[i];
        }
    }

    fn calculate_outputs(&mut self)
    {
        if self.m_size == 0 {return;}

        if self.m_size == 1
        {
            self.m_outputs[0] = self.m_inputs[0];
            return;
        }

        if self.m_size == 2 
        {
            
            if self.m_gates[0] == true
            {
                self.m_outputs[0] = self.m_inputs[1];
                self.m_outputs[1] = self.m_inputs[0];
            }
            else
            {
                self.m_outputs[0] = self.m_inputs[0];
                self.m_outputs[1] = self.m_inputs[1];
            }
            return;
        }

        if self.m_size == 3
        {
            if self.m_gates[0] == true
            {
                self.m_outputs[0] = self.m_inputs[1];
                self.m_outputs[1] = self.m_inputs[0];
            }
            else
            {
                self.m_outputs[0] = self.m_inputs[0];
                self.m_outputs[1] = self.m_inputs[1];
            }

            self.m_outputs[2] = self.m_inputs[2];

            if self.m_gates[2] == true // the "passthrough"
            {
                let tmp = self.m_outputs[1];
                self.m_outputs[1] = self.m_outputs[2];
                self.m_outputs[2] = tmp;
            }

            if self.m_gates[1] == true // the rightmost
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }
            return;
        }

        if self.m_size == 4
        {
            if self.m_gates[0] == true
            {
                self.m_outputs[0] = self.m_inputs[1];
                self.m_outputs[1] = self.m_inputs[0];
            }
            else
            {
                self.m_outputs[0] = self.m_inputs[0];
                self.m_outputs[1] = self.m_inputs[1];
            }
            
            if self.m_gates[1] == true
            {
                self.m_outputs[2] = self.m_inputs[3];
                self.m_outputs[3] = self.m_inputs[2];
            }
            else
            {
                self.m_outputs[2] = self.m_inputs[2];
                self.m_outputs[3] = self.m_inputs[3];
            }
            
            // first flip top only line 1 and 2 are flipped
            let tmp = self.m_outputs[1];
            self.m_outputs[1] = self.m_outputs[2];
            self.m_outputs[2] = tmp;

            if self.m_gates[3] == true // middle top gate
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }

            if self.m_gates[4] == true // middle bot gate
            {
                let tmp = self.m_outputs[2];
                self.m_outputs[2] = self.m_outputs[3];
                self.m_outputs[3] = tmp;
            }

            // final flip top only line 1 and 2 are flipped
            let tmp = self.m_outputs[1];
            self.m_outputs[1] = self.m_outputs[2];
            self.m_outputs[2] = tmp;

            if self.m_gates[2] == true // end top gate
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }
            return;
        }

        // size is at least 5
        let num_of_left_gates:usize = self.m_size / 2;
        let my_size = self.m_size;
        let mut tmp_input = vec![0; my_size];        
        // copy to tmp
        for i in 0..my_size
        {
            tmp_input[i] = self.m_inputs[i];
        }

        // first gate check
        for i in 0..num_of_left_gates
        {
            if self.m_gates[i] == true
            {
                let tmp = tmp_input[i*2];
                tmp_input[i * 2] = tmp_input[i * 2 + 1];
                tmp_input[i * 2 + 1] = tmp;
            }
        }

        let mut tmp_input_top = vec![0; num_of_left_gates];
        let mut tmp_input_bot = vec![0; my_size - num_of_left_gates];
        let mut countleft = 0;
        let mut countright = 0;       
        // spliting the inputs to top and bottom
        for i in 0..my_size
        {
            if i % 2 == 0 // counting from 0 is funny..
            {
                if i == (my_size - 1)
                {
                   tmp_input_bot[countright] = tmp_input[i];
                    countright += 1;
                }
                else
                {
                    tmp_input_top[countleft] = tmp_input[i];
                    countleft += 1;
                }  
            }
            else
            {
                tmp_input_bot[countright] = tmp_input[i];
                countright += 1;
            }
        }

        // copy back
        for i in 0..my_size
        {
            if i >= tmp_input_top.len()
            {
                tmp_input[i] = tmp_input_bot[i - tmp_input_top.len()];
            }
            else
            {
                tmp_input[i] = tmp_input_top[i];
            }
        }

        // send into recursive wakeman
        if self.m_top.len() != 0
        {
            let top_size = self.m_top[0].m_size;
            let mut tmp_top_input = vec![0; top_size];
            for i in 0..top_size
            {
                tmp_top_input[i] = tmp_input[i];
            }
            self.m_top[0].set_inputs(tmp_top_input);
            self.m_top[0].calculate_outputs();
        }

        if self.m_bot.len() != 0
        {
            let bot_size = self.m_bot[0].m_size;
            let mut tmp_bot_input = vec![0; bot_size];
            for i in 0..bot_size
            {
                let mut top_size_for_bot:usize = 0;
                if self.m_top.len() != 0
                {
                    top_size_for_bot = self.m_top[0].m_size;
                }
                let offset_counter_bottom = i + top_size_for_bot;
                if offset_counter_bottom >= my_size
                {
                    tmp_bot_input[i] = tmp_input[tmp_input.len()-1];
                }
                else
                {
                    tmp_bot_input[i] = tmp_input[offset_counter_bottom];
                }
            }
            self.m_bot[0].set_inputs(tmp_bot_input);
            self.m_bot[0].calculate_outputs();
        }

        // extraction of data from internal structures
        if self.m_top.len() != 0
        {
            let top_size:usize = self.m_top[0].m_size;
            for i in 0..top_size
            {
                tmp_input[i] = self.m_top[0].m_outputs[i];
            }
        }

        if self.m_bot.len() != 0
        {
            let bot_size:usize = self.m_bot[0].m_size;
            for i in 0..bot_size
            {
                let mut top_size_out:usize = 0;
                if self.m_top.len() != 0 
                {
                    top_size_out = self.m_top[0].m_size;
                }
                tmp_input[i + top_size_out] = self.m_bot[0].m_outputs[i];
            }
        }

        // last gate check
        let mut num_of_right_gates:usize = my_size / 2;
        if my_size % 2 == 0
        {
            num_of_right_gates -= 1
        }

        // spliting the inputs to top and bottom
        countleft = 0;
        countright = 0;
        for i in 0..my_size
        {
            if i % 2 == 0 // counting from 0 is funny..
            {
                if i == my_size - 1
                {
                    tmp_input_bot[countright] = tmp_input[i];
                    countright += 1;
                }
                else
                {
                    tmp_input_top[countleft] = tmp_input[i];
                    countleft += 1;
                }  
            }
            else
            {
                tmp_input_bot[countright] = tmp_input[i];
                countright += 1;
            }
        }

        // copy back
        for i in 0..my_size
        {
            if i >= tmp_input_top.len()
            {
                tmp_input[i] = tmp_input_bot[i - tmp_input_top.len()];
            }
            else
            {
                tmp_input[i] = tmp_input_top[i];
            }
        }

        for i in 0..num_of_right_gates
        {
            let counter_final_gate = i + num_of_left_gates - 1;
            if self.m_gates[counter_final_gate] == true 
            {
                let right_gate_tmp = tmp_input[i * 2];
                tmp_input[i * 2] = tmp_input[i * 2 + 1];
                tmp_input[i * 2 + 1] = right_gate_tmp;
            }
        }

        // copy to outputs
        for i in 0..my_size
        {
            self.m_outputs[i] = tmp_input[i];
        }
        return;
    }

    fn calculate_witness(self)-> Vec<bool>
    {
        let max_count = 2_u64.pow(self.m_gate_size as u32); // this is max permutations to bruteforce
        let failed_permuation = vec![];
        let mut cur_permuation = vec![false; self.m_gate_size];
        for j in 0..max_count
        {
            // change the configuration to handle stuffs.
            for i in 0..self.m_gate_size
            {
                let currentindex = j & (1 << i);
                if currentindex != 0
                {
                    cur_permuation[i] = true;
                }
                else
                {
                    cur_permuation[i] = false;
                }
            }


            // calculate a new permutation
            let mut test_aswaksman = ASWaksman::new_internal(self.m_size, self.m_inputs.clone(), self.m_outputs.clone(), cur_permuation.clone());
            test_aswaksman.calculate_outputs();

            let mut is_result_good = true;
            for i in 0..self.m_size
            {
                if test_aswaksman.m_outputs[i] != self.m_outputs[i]
                {
                    is_result_good = false;
                    break;
                }
            }

            if is_result_good
            {
                return cur_permuation;
            }
        }

        return failed_permuation;
    }

    #[allow(dead_code)]
    fn new(size: usize) -> ASWaksman
    {
        return ASWaksman::new_internal(size, vec![], vec![], vec![])
    }

    fn new_internal(size: usize, input: Vec<u32>, output: Vec<u32>, _gates: Vec<bool>) -> ASWaksman
    {
        let gate_size = ASWaksman::calculate_gate_size(size);
        let mut top = vec![];
        let mut bot = vec![];

        // recursive creation
        let top_size:usize = size / 2;
        let mut bot_size = top_size + 1;
        if size % 2 == 0 {bot_size = top_size}
        let rounded_down_gates:usize;
        if size % 2 == 0 {rounded_down_gates = size} else {rounded_down_gates = size - 1}

        // only split if its more than 4
        if size > 4
        {
            // handle gates
            // handle top gate
            let top_gate_size = ASWaksman::calculate_gate_size(top_size);
            let mut top_gates = vec![false; top_gate_size];
            if top_gate_size != 0
            {
                for i in 0..top_gate_size
                {
                    let offset_count = i + rounded_down_gates - 1;
                    top_gates[i] = _gates[offset_count];
                }
            }
            // handle bot gate
            let bot_gate_size = ASWaksman::calculate_gate_size(bot_size);
            let mut bot_gates = vec![false; bot_gate_size];
            if bot_gate_size != 0
            {
                for i in 0..bot_gate_size
                {                   
                    let offset_count = i + rounded_down_gates - 1 + top_gate_size;
                    bot_gates[i] = _gates[offset_count];
                }
            }

            // handle inputs
            // handle top half of aswakeman inputs
            let mut top_inputs = vec![0; top_size];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = i * 2; //-> 0, 2, 4
                    top_inputs[i] = input[offset_count];
                }
            }

            let mut bot_inputs = vec![0; bot_size];
            if bot_size != 0
            {
                for i in 0..bot_size
                {
                    let offset_count = (i * 2) + 1; // -> 1,3,5,7 i
                    if offset_count >= size
                    { 
                        bot_inputs[bot_size - 1] = input[offset_count - 1];
                    }
                    else
                    {
                        bot_inputs[i] = input[offset_count];
                    }
                    
                }
            }

            // handle outputs
            // handle top half of aswakeman outputs
            let mut top_outputs = vec![0; top_size];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = i*2;
                    top_outputs[i] = output[offset_count];
                }
            }

            let mut bot_outputs = vec![0; bot_size];
            if bot_size != 0
            {
                for i in 0..bot_size
                {
                    let offset_count = (i*2) + 1;
                    if offset_count >= (size) {break;}
                    bot_outputs[i] = output[offset_count];
                }
            }

            // recursive construction
            if top_size > 1
            {
                top.push(ASWaksman::new_internal(top_size, top_inputs, top_outputs, top_gates));
            }

            if bot_size > 1
            {
                bot.push(ASWaksman::new_internal(bot_size, bot_inputs, bot_outputs, bot_gates));
            }
        }
        return ASWaksman 
        {
            m_top: top,
            m_bot: bot,
            m_gate_size: gate_size,
            m_size: size,
            m_inputs: input,
            m_outputs: output,
            m_gates: _gates,
        };
    }

    #[allow(dead_code)]
    fn print(&self) -> String
    {
        return String::from(format!("ASWaksman: {} {:?} {:?} {:?}",self.m_size, self.m_inputs, self.m_outputs, self.m_gates));
    }
}
