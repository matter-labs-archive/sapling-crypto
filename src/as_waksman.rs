pub struct ASWaksman
{
    m_top: Vec<ASWaksman>,
    m_bot: Vec<ASWaksman>,
    m_gate_size: u32,
    m_size: u32,
    m_inputs: Vec<u32>,
    m_outputs: Vec<u32>,
    m_gates: Vec<bool>,
}

impl ASWaksman
{
    fn calculate_gate_size(size: u32) -> u32
    {
        if size == 0 {return 0;}
        if size == 1 {return 1;}
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

            if self.m_gates[4] == true // middle gate
            {
                let tmp = self.m_outputs[1];
                self.m_outputs[1] = self.m_outputs[2];
                self.m_outputs[2] = tmp;
            }

            if self.m_gates[2] == true // end top gate
            {
                let tmp = self.m_outputs[0];
                self.m_outputs[0] = self.m_outputs[1];
                self.m_outputs[1] = tmp;
            }

            if self.m_gates[3] == true // end bot gate
            {
                let tmp = self.m_outputs[2];
                self.m_outputs[2] = self.m_outputs[3];
                self.m_outputs[3] = tmp;
            }
            return;
        }

        // if im here, im at at least size 5.
        // first pass
        let num_of_left_gates = self.m_size / 2;
        let mut tmp_input = vec![0; self.m_size as usize];
        for i in 0..self.m_size as usize
        {           
            tmp_input[i] = self.m_inputs[i];
        }
        println!("fp: {:?} {:?} s:{}", tmp_input, self.m_inputs, self.m_size);

        // first gate check
        for i in 0..num_of_left_gates as usize
        {
            if self.m_gates[i] == true
            {
                let tmp = tmp_input[i*2];
                tmp_input[i*2] = tmp_input[i*2 +1 ];
                tmp_input[i*2+1] = tmp;
            }
        }

        // todo:: re direct inputs

        println!("fg: {:?} {:?} s:{}", tmp_input, self.m_inputs, self.m_size);
        // send into recursive wakeman
        if self.m_top.len() != 0
        {
            let top_size = self.m_top[0].m_size;
            let mut tmp_top_input = vec![0; top_size as usize];
            for i in 0..top_size as u32
            {
                tmp_top_input[i as usize] = tmp_input[i as usize];
            }
            println!("top calc {} {:?}" , top_size, tmp_top_input);
            self.m_top[0].set_inputs(tmp_top_input);
            self.m_top[0].calculate_outputs();
            println!("top result {:?}" , self.m_top[0].m_outputs);
        }

        if self.m_bot.len() != 0
        {
            let bot_size = self.m_bot[0].m_size;
            let mut tmp_bot_input = vec![0; bot_size as usize];
            for i in 0..bot_size as u32
            {
                let mut top_size_for_bot = 0;
                if self.m_top.len() != 0
                {
                    top_size_for_bot = self.m_top[0].m_size;
                }
                let offset_counter_bottom = i + top_size_for_bot;
                if offset_counter_bottom >= self.m_size
                {
                    tmp_bot_input[i as usize] = tmp_input[tmp_input.len()-1];
                }
                else
                {
                    tmp_bot_input[i as usize] = tmp_input[offset_counter_bottom as usize];
                }
            }
            println!("bot calc {} {:?}" , bot_size, tmp_bot_input);
            self.m_bot[0].set_inputs(tmp_bot_input);
            self.m_bot[0].calculate_outputs();
            println!("bot result {:?}" , self.m_bot[0].m_outputs);
        }

        // extraction of data from internal structures
        if self.m_top.len() != 0
        {
            let top_size = self.m_top[0].m_size;
            for i in 0..top_size
            {
                tmp_input[i as usize] = self.m_top[0].m_outputs[i as usize];
            }
        }

        if self.m_bot.len() != 0
        {
            let bot_size = self.m_bot[0].m_size;
            for i in 0..bot_size
            {
                let mut top_size_out = 0;
                if self.m_top.len() != 0 
                {
                    top_size_out = self.m_top[0].m_size;
                }
                tmp_input[(i + top_size_out) as usize] = self.m_bot[0].m_outputs[i as usize];
            }
        }
        println!("e: {:?} t:{:?} b:{:?} s:{}", tmp_input, self.m_top[0].m_outputs,self.m_bot[0].m_outputs, self.m_size);
        // last gate check
        for i in 0..num_of_left_gates as usize
        {
            let counter_final_gate = (i as u32 + num_of_left_gates - 1) as usize;
            if self.m_gates[counter_final_gate] == true 
            {
                let right_gate_tmp = tmp_input[i * 2];
                tmp_input[i * 2] = tmp_input[i * 2 + 1];
                tmp_input[i * 2 + 1] = right_gate_tmp;
            }
        }
        println!("lg: {:?} {:?} s:{}", tmp_input, self.m_inputs, self.m_size);
        // copy to outputs
        for i in 0..self.m_size as usize
        {
            self.m_outputs[i] = tmp_input[i];
        }
        return;
    }

    fn calculate_witness(self)-> Vec<bool>
    {
        return vec![false];
    }

    fn new(size: u32) -> ASWaksman
    {
        return ASWaksman::new_internal(size, vec![], vec![], vec![])
    }

    fn new_internal(size: u32, input: Vec<u32>, output: Vec<u32>, _gates: Vec<bool>) -> ASWaksman
    {
        println!("start {}" , size);
        let gate_size = ASWaksman::calculate_gate_size(size);
        let mut top = vec![];
        let mut bot = vec![];

        // recursive creation
        let top_size:u32 = size / 2;
        let mut bot_size:u32;
        if size % 2 == 0 {bot_size = top_size} else {bot_size = top_size + 1}
        let rounded_down_gates:u32;
        if size % 2 == 0 {rounded_down_gates = size} else {rounded_down_gates = size - 1}
        let left_over_gates = size - rounded_down_gates;
        if size < 5
        {
            // too small a aswakeman, no need to spilt.
        }
        else
        {
            // handle gates
            // handle top gate
            let top_gate_size = ASWaksman::calculate_gate_size(top_size);
            let mut top_gates = vec![false; top_gate_size as usize];
            if top_gate_size != 0
            {
                for i in 0..top_gate_size
                {
                    let offset_count = (i + rounded_down_gates - 1) as usize;
                    top_gates[i as usize] = _gates[offset_count];
                }
            }
            // handle bot gate
            let bot_gate_size = ASWaksman::calculate_gate_size(bot_size);
            let mut bot_gates = vec![false; bot_gate_size as usize];
            if bot_gate_size != 0
            {
                for i in 0..bot_gate_size
                {                   
                    let offset_count = (i + rounded_down_gates - 1 + top_gate_size) as usize;
                    bot_gates[i as usize] = _gates[offset_count];
                }
            }

            // handle inputs
            // handle top half of aswakeman inputs
            let mut top_inputs = vec![0; top_size as usize];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = (i*2) as usize; //-> 0, 2, 4
                    top_inputs[i as usize] = input[offset_count];
                }
            }

            let mut bot_inputs = vec![0; bot_size as usize];
            if bot_size != 0
            {
                //println!("botsize {}", bot_size);
                for i in 0..bot_size
                {
                    let offset_count = ((i*2) + 1) as usize; // -> 1,3,5,7 i
                    //println!("oc:{} i:{} s:{} b_s:{}", offset_count , i, size, bot_size);
                    if offset_count >= (size as usize)
                    { 
                        bot_inputs[(bot_size - 1) as usize] = input[(offset_count - 1) as usize];
                    }
                    else
                    {
                        bot_inputs[i as usize] = input[offset_count];
                    }
                    
                }
            }
            println!("topinputs {:?}", top_inputs);
            println!("botinputs {:?}", bot_inputs);

            // handle outputs
            // handle top half of aswakeman outputs
            let mut top_outputs = vec![0; top_size as usize];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = (i*2) as usize;
                    top_outputs[i as usize] = output[offset_count];
                }
            }

            let mut bot_outputs = vec![0; bot_size as usize];
            if bot_size != 0
            {
                for i in 0..bot_size
                {
                    let offset_count = ((i*2) + 1) as usize;
                    if offset_count >= (size as usize) {break;}
                    bot_outputs[i as usize] = output[offset_count];
                }
            }

            // reconstruct
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

    fn print(&self) -> String
    {
        //return String::from(format!("ASWaksman: {} {:?} {:?}",self.m_size, self.m_inputs, self.m_outputs));
        return String::from(format!("ASWaksman: {} {:?} {:?} {:?}",self.m_size, self.m_inputs, self.m_outputs, self.m_gates));
    }
}

fn main()
{
    for i in 5..6
    {
        let mut count = vec![];
        for j in 0..i
        {
            count.push(j);
        }
        let mut b = ASWaksman::new_internal(i,count, vec![0; i as usize], vec![true; ASWaksman::calculate_gate_size(i) as usize]);
        b.calculate_outputs();
        println!("{}", b.print());
    }

    // for i in 0..5
    // {
    //     let mut count = vec![];
    //     for j in 0..i
    //     {
    //         count.push(j);
    //     }
    //     let mut b = ASWaksman::new_internal(i,count, vec![0; i as usize], vec![false; ASWaksman::calculate_gate_size(i) as usize]);
    //     b.calculate_outputs();
    //     println!("{}", b.print());
    // }

    // for i in 0..5
    // {
    //     let mut count = vec![];
    //     for j in 0..i
    //     {
    //         count.push(j);
    //     }
    //     let mut b = ASWaksman::new_internal(i,count, vec![0; i as usize], vec![true; ASWaksman::calculate_gate_size(i) as usize]);
    //     b.calculate_outputs();
    //     println!("{}", b.print());
    // }
}
