pub struct ASWaksman
{
    m_top: Vec<ASWaksman>,
    m_bottom: Vec<ASWaksman>,
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
        if size < 2 {return 0;}
        let is_odd = size % 2 != 0;
        if is_odd == true
        {
            return ASWaksman::calculate_gate_size((size / 2) + 1) + ASWaksman::calculate_gate_size(size / 2) + size - 1;
        }
        return ASWaksman::calculate_gate_size(size / 2) + ASWaksman::calculate_gate_size(size / 2) + size - 1;
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
            return;
        }

        // todo: normal stuffs here
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
        let gate_size = ASWaksman::calculate_gate_size(size);
        let mut top = vec![];
        let mut bot = vec![];

        // recursive creation
        let top_size:u32 = size / 2;
        let bot_size:u32;
        if size % 2 == 0 {bot_size = top_size} else {bot_size = top_size + 1}
        let rounded_down_gates:u32;
        if size % 2 == 0 {rounded_down_gates = size} else {rounded_down_gates = size - 1}
        let left_over_gates = size - rounded_down_gates;
        if left_over_gates > 0
        {
            // handle gates
            // handle top gate
            let top_gate_size = ASWaksman::calculate_gate_size(top_size);
            let mut top_gates = vec![];
            if top_gate_size != 0
            {
                for i in 0..top_gate_size
                {
                    let offset_count = (i + rounded_down_gates - 1) as usize;
                    top_gates.push(_gates[offset_count]);
                }
            }
            // handle bot gate
            let bot_gate_size = ASWaksman::calculate_gate_size(bot_size);
            let mut bot_gates = vec![];
            if bot_gate_size != 0
            {
                for i in 0..bot_gate_size
                {                   
                    let offset_count = (i + rounded_down_gates - 1 + top_gate_size) as usize;
                    bot_gates.push(_gates[offset_count]);
                }
            }

            // handle inputs
            // handle top half of aswakeman inputs
            let mut top_inputs = vec![];
            if top_size != 0
            {
                for i in 0..top_size
                {
                    let offset_count = (i*2) as usize;
                    top_inputs.push(input[offset_count]);
                }
            }

            let mut bot_inputs = vec![];
            if bot_size != 0
            {
                for i in 0..bot_size
                {
                    let offset_count = ((i*2) + 1) as usize;
                    if offset_count >= (size as usize) {break;}
                    bot_inputs.push(input[offset_count]);
                }
            }

            // reconstruct
            if top_size > 1
            {
                top.push(ASWaksman::new_internal(top_size, vec![0; top_size as usize], vec![0; top_size as usize], vec![false; ASWaksman::calculate_gate_size(top_size) as usize]));
            }

            if bot_size > 1
            {
                bot.push(ASWaksman::new_internal(bot_size, vec![0; bot_size as usize], vec![0; bot_size as usize], vec![false; ASWaksman::calculate_gate_size(bot_size) as usize]));
            }
        }
        return ASWaksman
        {
            m_top: top,
            m_bottom: bot,
            m_gate_size: gate_size,
            m_size: size,
            m_inputs: input,
            m_outputs: output,
            m_gates: _gates,
        };
    }

    fn print(&self) -> String
    {
        return String::from(format!("ASWaksman: {} {:?} {:?} {:?}",self.m_size, self.m_inputs, self.m_outputs, self.m_gates));
    }
}
